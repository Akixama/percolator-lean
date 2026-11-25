use litesvm::LiteSVM;
use solana_account::Account;
use solana_address::Address;
use solana_clock::Clock;
use solana_instruction::{AccountMeta, Instruction};
use solana_keypair::Keypair;
use solana_message::Message;
use solana_signer::Signer;
use solana_transaction::Transaction;

const TOKEN_PROGRAM_ID: Address =
    Address::from_str_const("TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA");
const SYSTEM_PROGRAM_ID: Address =
    Address::from_str_const("11111111111111111111111111111111");
const SPL_TOKEN_RENT_MIN: u64 = 2_039_280;

// Exact v2 layout constants matching Percolator/Layout.lean
const DEX_SIZE: usize = 200;
const MKT_SIZE: usize = 352;
const PFL_SIZE: usize = 952;
const INS_SIZE: usize = 88;
const MAX_LEGS: usize = 8;
const LEG_HEADER: usize = 120;
const LEG_STRIDE: usize = 104;
const POS_SCALE: u64 = 1_000_000;
const ADL_ONE: u64 = 1_000_000_000;

fn make_spl_mint(decimals: u8, supply: u64, mint_auth: &Address) -> Vec<u8> {
    let mut data = vec![0u8; 82];
    data[0..4].copy_from_slice(&1u32.to_le_bytes());
    data[4..36].copy_from_slice(mint_auth.as_ref());
    data[36..44].copy_from_slice(&supply.to_le_bytes());
    data[44] = decimals;
    data[45] = 1;
    data
}

fn make_spl_token_account(mint: &Address, owner: &Address, amount: u64) -> Vec<u8> {
    let mut data = vec![0u8; 165];
    data[0..32].copy_from_slice(mint.as_ref());
    data[32..64].copy_from_slice(owner.as_ref());
    data[64..72].copy_from_slice(&amount.to_le_bytes());
    data[108] = 1; // Initialized
    data
}

fn token_amount(svm: &LiteSVM, acc: &Address) -> u64 {
    let a = svm.get_account(acc).expect("token acc missing");
    u64::from_le_bytes(a.data[64..72].try_into().unwrap())
}

fn read_u64(svm: &LiteSVM, acc: &Address, off: usize) -> u64 {
    let a = svm.get_account(acc).expect("acc missing");
    u64::from_le_bytes(a.data[off..off + 8].try_into().unwrap())
}

fn read_u8(svm: &LiteSVM, acc: &Address, off: usize) -> u8 {
    let a = svm.get_account(acc).expect("acc missing");
    a.data[off]
}

fn set_slot(svm: &mut LiteSVM, slot: u64) {
    let mut clock: Clock = svm.get_sysvar();
    clock.slot = slot;
    svm.set_sysvar(&clock);
    svm.expire_blockhash();
}

fn get_slot(svm: &LiteSVM) -> u64 {
    let clock: Clock = svm.get_sysvar();
    clock.slot
}

fn compact_u16_len(n: usize) -> usize {
    if n < 0x80 { 1 } else if n < 0x4000 { 2 } else { 3 }
}

/// Exact Solana legacy wire transaction byte length (must be <= 1,232 bytes for UDP MTU!).
fn legacy_tx_wire_bytes(tx: &Transaction) -> usize {
    let sigs = tx.signatures.len();
    let msg = &tx.message;
    let keys = msg.account_keys.len();
    let ixs = &msg.instructions;
    let mut len = compact_u16_len(sigs) + sigs * 64;
    len += 3; // MessageHeader
    len += compact_u16_len(keys) + keys * 32;
    len += 32; // recent_blockhash
    len += compact_u16_len(ixs.len());
    for ix in ixs {
        len += 1; // program_id_index
        len += compact_u16_len(ix.accounts.len()) + ix.accounts.len();
        len += compact_u16_len(ix.data.len()) + ix.data.len();
    }
    len
}

fn send_ixs_ok_measured(svm: &mut LiteSVM, ixs: &[Instruction], payer: &Keypair, signers: &[&Keypair]) -> (u64, usize) {
    svm.expire_blockhash();
    let bh = svm.latest_blockhash();
    let msg = Message::new(ixs, Some(&payer.pubkey()));
    let tx = Transaction::new(signers, msg, bh);
    let wire = legacy_tx_wire_bytes(&tx);
    let res = svm.send_transaction(tx).unwrap_or_else(|e| panic!("Expected OK (wire={}B), got {:?}", wire, e));
    (res.compute_units_consumed, wire)
}

fn send_ixs_ok(svm: &mut LiteSVM, ixs: &[Instruction], payer: &Keypair, signers: &[&Keypair]) -> u64 {
    send_ixs_ok_measured(svm, ixs, payer, signers).0
}

fn send_ok(svm: &mut LiteSVM, ix: Instruction, payer: &Keypair, signers: &[&Keypair]) -> u64 {
    send_ixs_ok(svm, &[ix], payer, signers)
}

fn send_ok_assert_log(
    svm: &mut LiteSVM,
    ix: Instruction,
    payer: &Keypair,
    signers: &[&Keypair],
    expected_prefix: &str,
) -> u64 {
    svm.expire_blockhash();
    let bh = svm.latest_blockhash();
    let msg = Message::new(&[ix], Some(&payer.pubkey()));
    let tx = Transaction::new(signers, msg, bh);
    let res = svm.send_transaction(tx).unwrap_or_else(|e| panic!("Expected OK, got {:?}", e));
    assert!(
        res.logs.iter().any(|l| l.contains(expected_prefix)),
        "Expected structured log containing '{}' in logs: {:?}",
        expected_prefix,
        res.logs
    );
    res.compute_units_consumed
}

fn send_ixs_err(svm: &mut LiteSVM, ixs: &[Instruction], payer: &Keypair, signers: &[&Keypair], label: &str) {
    svm.expire_blockhash();
    let bh = svm.latest_blockhash();
    let msg = Message::new(ixs, Some(&payer.pubkey()));
    let tx = Transaction::new(signers, msg, bh);
    let res = svm.send_transaction(tx);
    assert!(res.is_err(), "Expected rejection for '{}', but tx succeeded!", label);
}

fn send_ixs_try(svm: &mut LiteSVM, ixs: &[Instruction], payer: &Keypair, signers: &[&Keypair]) -> Result<u64, String> {
    svm.expire_blockhash();
    let bh = svm.latest_blockhash();
    let msg = Message::new(ixs, Some(&payer.pubkey()));
    let tx = Transaction::new(signers, msg, bh);
    svm.send_transaction(tx)
        .map(|r| r.compute_units_consumed)
        .map_err(|e| format!("{:?}", e))
}

fn send_err(svm: &mut LiteSVM, ix: Instruction, payer: &Keypair, signers: &[&Keypair], label: &str) {
    svm.expire_blockhash();
    let bh = svm.latest_blockhash();
    let msg = Message::new(&[ix], Some(&payer.pubkey()));
    let tx = Transaction::new(signers, msg, bh);
    let res = svm.send_transaction(tx);
    assert!(res.is_err(), "Expected rejection for '{}', but tx succeeded!", label);
}

fn send_err_custom(
    svm: &mut LiteSVM,
    ix: Instruction,
    payer: &Keypair,
    signers: &[&Keypair],
    expected_code: u32,
    label: &str,
) {
    svm.expire_blockhash();
    let bh = svm.latest_blockhash();
    let msg = Message::new(&[ix], Some(&payer.pubkey()));
    let tx = Transaction::new(signers, msg, bh);
    let res = svm.send_transaction(tx);
    let err = res.expect_err(&format!(
        "Expected Custom({}) rejection for '{}', but tx SUCCEEDED!",
        expected_code, label
    ));
    let dbg = format!("{:?}", err);
    let needle = format!("Custom({})", expected_code);
    assert!(
        dbg.contains(&needle),
        "Expected {} for '{}', got: {}",
        needle,
        label,
        dbg
    );
}

fn create_prog_acc(svm: &mut LiteSVM, prog_id: &Address, size: usize) -> Address {
    let addr = Keypair::new().pubkey();
    svm.set_account(
        addr,
        Account {
            lamports: 10_000_000,
            data: vec![0u8; size],
            owner: *prog_id,
            executable: false,
            rent_epoch: 0,
        },
    )
    .unwrap();
    addr
}

fn create_tok_acc(svm: &mut LiteSVM, mint: &Address, owner: &Address, amount: u64) -> Address {
    let addr = Keypair::new().pubkey();
    svm.set_account(
        addr,
        Account {
            lamports: 10_000_000,
            data: make_spl_token_account(mint, owner, amount),
            owner: TOKEN_PROGRAM_ID,
            executable: false,
            rent_epoch: 0,
        },
    )
    .unwrap();
    addr
}

/// Pure PDA derivation ONLY — does NOT mock or create the account!
/// `InitDex` itself creates & initializes the SPL Token vault account on-chain via CPI!
fn derive_dex_vault(prog_id: &Address, dex: &Address) -> (Address, u8) {
    Address::find_program_address(&[b"dvlt", dex.as_ref()], prog_id)
}

/// Global + per-market + per-portfolio EXACT invariant verifier!
fn assert_dex_invariants(
    svm: &LiteSVM,
    dex: &Address,
    dex_vault: &Address,
    markets: &[Address],
    portfolios: &[Address],
    label: &str,
) {
    let v = read_u64(svm, dex, 160);
    let c_tot = read_u64(svm, dex, 168);
    let i_tot = read_u64(svm, dex, 176);
    let r_tot = read_u64(svm, dex, 184);
    let s_tot = read_u64(svm, dex, 192);
    let spl = token_amount(svm, dex_vault);

    assert_eq!(v, spl, "[{}] Dex.vaultBalance ({}) != SPL balance ({})", label, v, spl);
    assert_eq!(
        c_tot as u128 + i_tot as u128 + r_tot as u128 + s_tot as u128,
        v as u128,
        "[{}] EXACT stock equality violated: C({}) + I({}) + R({}) + S({}) != V({})",
        label, c_tot, i_tot, r_tot, s_tot, v
    );

    let mut sum_i: u64 = 0;
    let mut sum_r: u64 = 0;
    let mut sum_s: u64 = 0;
    for m in markets {
        let r_m = read_u64(svm, m, 216);
        let i_m = read_u64(svm, m, 224);
        let s_m = read_u64(svm, m, 232);
        let oi_l = read_u64(svm, m, 256);
        let oi_s = read_u64(svm, m, 264);
        let raw_l = read_u64(svm, m, 272);
        let raw_s = read_u64(svm, m, 280);
        let adl_l = read_u64(svm, m, 288);
        let adl_s = read_u64(svm, m, 296);
        let max_oi = read_u64(svm, m, 208);

        assert_eq!(oi_l, oi_s, "[{}] Market OI imbalanced: {} != {}", label, oi_l, oi_s);
        assert!(oi_l <= max_oi, "[{}] Market OI {} > maxOi {}", label, oi_l, max_oi);
        assert!(oi_l <= raw_l, "[{}] oiLong {} > rawBasisLong {}", label, oi_l, raw_l);
        assert!(oi_s <= raw_s, "[{}] oiShort {} > rawBasisShort {}", label, oi_s, raw_s);
        assert!(adl_l <= ADL_ONE, "[{}] adlLong {} > ADL_ONE", label, adl_l);
        assert!(adl_s <= ADL_ONE, "[{}] adlShort {} > ADL_ONE", label, adl_s);
        sum_i += i_m;
        sum_r += r_m;
        sum_s += s_m;
    }
    assert_eq!(sum_i, i_tot, "[{}] Σ m.insurance ({}) != Dex.totalInsurance ({})", label, sum_i, i_tot);
    assert_eq!(sum_r, r_tot, "[{}] Σ m.realizedPool ({}) != Dex.totalResidual ({})", label, sum_r, r_tot);
    assert!(sum_s <= s_tot, "[{}] Σ m.feeSurplus ({}) > Dex.totalSurplus ({})", label, sum_s, s_tot);

    let mut sum_c: u64 = 0;
    for p in portfolios {
        let cap = read_u64(svm, p, 88);
        let tot_mm = read_u64(svm, p, 96);
        let tot_im = read_u64(svm, p, 104);
        let tot_res = read_u64(svm, p, 112);
        let leg_cnt = read_u8(svm, p, 4);
        let mut calc_mm: u64 = 0;
        let mut calc_im: u64 = 0;
        let mut calc_res: u64 = 0;
        let mut calc_cnt: u8 = 0;
        for idx in 0..MAX_LEGS {
            let base = LEG_HEADER + idx * LEG_STRIDE;
            if read_u8(svm, p, base) != 0 {
                let l_mm = read_u64(svm, p, base + 72);
                let l_im = read_u64(svm, p, base + 80);
                let l_res = read_u64(svm, p, base + 96);
                assert!(l_res <= l_mm, "[{}] Leg reservedMm ({}) > cachedMm ({})", label, l_res, l_mm);
                calc_cnt += 1;
                calc_mm += l_mm;
                calc_im += l_im;
                calc_res += l_res;
            }
        }
        assert_eq!(calc_mm, tot_mm, "[{}] Portfolio totalMm mismatch: calc {} != stored {}", label, calc_mm, tot_mm);
        assert_eq!(calc_im, tot_im, "[{}] Portfolio totalIm mismatch: calc {} != stored {}", label, calc_im, tot_im);
        assert_eq!(calc_res, tot_res, "[{}] Portfolio totalReservedMm mismatch: calc {} != stored {}", label, calc_res, tot_res);
        assert!(tot_res <= cap, "[{}] ANTI-SHIELDING VIOLATED: totalReservedMm ({}) > capital ({})", label, tot_res, cap);
        assert_eq!(calc_cnt, leg_cnt, "[{}] Portfolio legCount mismatch: calc {} != stored {}", label, calc_cnt, leg_cnt);
        sum_c += cap;
    }
    assert_eq!(sum_c, c_tot, "[{}] Σ pfl.capital ({}) != Dex.totalCapital ({})", label, sum_c, c_tot);
}

// ============================================================================
// Instruction Builders (19 Unified v2 Instructions)
// ============================================================================

fn ix_init_dex(
    prog: Address, dex: Address, admin: Address, mint: Address,
    vault_pda: Address, fee_vault: Address, tok_prog: Address, sys_prog: Address,
    bump: u8, decimals: u8, create_fee: u64, rent_lamports: u64,
) -> Instruction {
    let mut data = vec![0u8; 20];
    data[0] = 0;
    data[1] = bump;
    data[2] = decimals;
    data[4..12].copy_from_slice(&create_fee.to_le_bytes());
    data[12..20].copy_from_slice(&rent_lamports.to_le_bytes());
    Instruction {
        program_id: prog,
        accounts: vec![
            AccountMeta::new(dex, false),
            AccountMeta::new(admin, true),
            AccountMeta::new_readonly(mint, false),
            AccountMeta::new(vault_pda, false),
            AccountMeta::new_readonly(fee_vault, false),
            AccountMeta::new_readonly(tok_prog, false),
            AccountMeta::new_readonly(sys_prog, false),
        ],
        data,
    }
}

fn ix_update_create_fee(prog: Address, dex: Address, admin: Address, new_fee: u64, new_admin: Option<Address>) -> Instruction {
    let mut data = vec![0u8; 9];
    data[0] = 1;
    data[1..9].copy_from_slice(&new_fee.to_le_bytes());
    let mut accounts = vec![AccountMeta::new(dex, false), AccountMeta::new_readonly(admin, true)];
    if let Some(na) = new_admin {
        accounts.push(AccountMeta::new_readonly(na, false));
    }
    Instruction { program_id: prog, accounts, data }
}

#[allow(clippy::too_many_arguments)]
fn ix_create_market_ext(
    prog: Address, dex: Address, mkt: Address, mint: Address, oracle_auth: Address,
    creator: Address, creator_tok: Address, fee_vault: Address,
    init_price: u64, exit_window: u64, max_staleness: u64, warmup_slots: u64,
    im_bps: u64, mm_bps: u64, liq_fee_bps: u64, trade_fee_bps: u64,
    max_move_bps: u64, max_ins_draw_bps: u64, max_oi: u64, min_mm: u64,
) -> Instruction {
    let mut data = vec![0u8; 100];
    data[0] = 2;
    data[4..12].copy_from_slice(&init_price.to_le_bytes());
    data[12..20].copy_from_slice(&exit_window.to_le_bytes());
    data[20..28].copy_from_slice(&max_staleness.to_le_bytes());
    data[28..36].copy_from_slice(&warmup_slots.to_le_bytes());
    data[36..44].copy_from_slice(&im_bps.to_le_bytes());
    data[44..52].copy_from_slice(&mm_bps.to_le_bytes());
    data[52..60].copy_from_slice(&liq_fee_bps.to_le_bytes());
    data[60..68].copy_from_slice(&trade_fee_bps.to_le_bytes());
    data[68..76].copy_from_slice(&max_move_bps.to_le_bytes());
    data[76..84].copy_from_slice(&max_ins_draw_bps.to_le_bytes());
    data[84..92].copy_from_slice(&max_oi.to_le_bytes());
    data[92..100].copy_from_slice(&min_mm.to_le_bytes());
    Instruction {
        program_id: prog,
        accounts: vec![
            AccountMeta::new(dex, false),
            AccountMeta::new(mkt, false),
            AccountMeta::new_readonly(mint, false),
            AccountMeta::new_readonly(oracle_auth, false),
            AccountMeta::new_readonly(creator, true),
            AccountMeta::new(creator_tok, false),
            AccountMeta::new(fee_vault, false),
            AccountMeta::new_readonly(TOKEN_PROGRAM_ID, false),
        ],
        data,
    }
}

#[allow(clippy::too_many_arguments)]
fn ix_create_market(
    prog: Address, dex: Address, mkt: Address, mint: Address, oracle_auth: Address,
    creator: Address, creator_tok: Address, fee_vault: Address,
    init_price: u64, exit_window: u64, max_staleness: u64, warmup_slots: u64,
    im_bps: u64, mm_bps: u64, liq_fee_bps: u64, trade_fee_bps: u64,
    max_move_bps: u64, max_ins_draw_bps: u64, max_oi: u64,
) -> Instruction {
    ix_create_market_ext(prog, dex, mkt, mint, oracle_auth, creator, creator_tok, fee_vault,
        init_price, exit_window, max_staleness, warmup_slots, im_bps, mm_bps, liq_fee_bps,
        trade_fee_bps, max_move_bps, max_ins_draw_bps, max_oi, 0)
}

fn ix_burn_market_admin(prog: Address, mkt: Address, admin: Address) -> Instruction {
    Instruction {
        program_id: prog,
        accounts: vec![AccountMeta::new(mkt, false), AccountMeta::new_readonly(admin, true)],
        data: vec![3, 0],
    }
}

fn ix_update_market_auth(prog: Address, mkt: Address, admin: Address, role: u8, new_key: Address) -> Instruction {
    Instruction {
        program_id: prog,
        accounts: vec![
            AccountMeta::new(mkt, false),
            AccountMeta::new_readonly(admin, true),
            AccountMeta::new_readonly(new_key, false),
        ],
        data: vec![3, role],
    }
}

fn ix_close_account(prog: Address, acc: Address, authority: Address, dest: Address) -> Instruction {
    Instruction {
        program_id: prog,
        accounts: vec![
            AccountMeta::new(acc, false),
            AccountMeta::new_readonly(authority, true),
            AccountMeta::new(dest, false),
        ],
        data: vec![19],
    }
}

#[allow(clippy::too_many_arguments)]
fn ix_liquidate_ext(
    prog: Address, dex: Address, mkt: Address, pfl: Address,
    liq_tok: Address, mint: Address, vault_pda: Address, tok_prog: Address,
    mode: u8, req_qty: u64, takeover: Option<(Address, Address)>,
) -> Instruction {
    let mut data = vec![0u8; 10];
    data[0] = 12;
    data[1] = mode;
    data[2..10].copy_from_slice(&req_qty.to_le_bytes());
    let mut accounts = vec![
        AccountMeta::new(dex, false),
        AccountMeta::new(mkt, false),
        AccountMeta::new(pfl, false),
        AccountMeta::new(liq_tok, false),
        AccountMeta::new_readonly(mint, false),
        AccountMeta::new(vault_pda, false),
        AccountMeta::new_readonly(tok_prog, false),
    ];
    if let Some((liq_pfl, liq_owner)) = takeover {
        accounts.push(AccountMeta::new(liq_pfl, false));
        accounts.push(AccountMeta::new_readonly(liq_owner, true));
    }
    Instruction { program_id: prog, accounts, data }
}

fn ix_update_oracle(prog: Address, mkt: Address, oracle_auth: Address, new_price: u64, fund_sign: u8, fund_e6: u64) -> Instruction {
    let mut data = vec![0u8; 18];
    data[0] = 4;
    data[1..9].copy_from_slice(&new_price.to_le_bytes());
    data[9] = fund_sign;
    data[10..18].copy_from_slice(&fund_e6.to_le_bytes());
    Instruction {
        program_id: prog,
        accounts: vec![AccountMeta::new(mkt, false), AccountMeta::new_readonly(oracle_auth, true)],
        data,
    }
}

fn ix_init_portfolio(prog: Address, dex: Address, pfl: Address, owner: Address) -> Instruction {
    Instruction {
        program_id: prog,
        accounts: vec![
            AccountMeta::new(dex, false),
            AccountMeta::new(pfl, false),
            AccountMeta::new_readonly(owner, true),
        ],
        data: vec![5],
    }
}

fn ix_deposit_collateral(
    prog: Address, dex: Address, pfl: Address, owner: Address,
    owner_tok: Address, mint: Address, vault_pda: Address, tok_prog: Address, amount: u64,
) -> Instruction {
    let mut data = vec![0u8; 9];
    data[0] = 6;
    data[1..9].copy_from_slice(&amount.to_le_bytes());
    Instruction {
        program_id: prog,
        accounts: vec![
            AccountMeta::new(dex, false),
            AccountMeta::new(pfl, false),
            AccountMeta::new_readonly(owner, true),
            AccountMeta::new(owner_tok, false),
            AccountMeta::new_readonly(mint, false),
            AccountMeta::new(vault_pda, false),
            AccountMeta::new_readonly(tok_prog, false),
        ],
        data,
    }
}

fn ix_withdraw_collateral(
    prog: Address, dex: Address, pfl: Address, owner: Address,
    dest_tok: Address, mint: Address, vault_pda: Address, tok_prog: Address, amount: u64,
) -> Instruction {
    let mut data = vec![0u8; 9];
    data[0] = 7;
    data[1..9].copy_from_slice(&amount.to_le_bytes());
    Instruction {
        program_id: prog,
        accounts: vec![
            AccountMeta::new(dex, false),
            AccountMeta::new(pfl, false),
            AccountMeta::new_readonly(owner, true),
            AccountMeta::new(dest_tok, false),
            AccountMeta::new_readonly(mint, false),
            AccountMeta::new(vault_pda, false),
            AccountMeta::new_readonly(tok_prog, false),
        ],
        data,
    }
}

fn ix_deposit_insurance_ext(
    prog: Address, dex: Address, mkt: Address, receipt: Address, lp: Address,
    lp_tok: Address, mint: Address, vault_pda: Address, tok_prog: Address, amount: u64, donate: bool,
) -> Instruction {
    let mut data = vec![0u8; 10];
    data[0] = 8;
    data[1..9].copy_from_slice(&amount.to_le_bytes());
    data[9] = if donate { 1 } else { 0 };
    Instruction {
        program_id: prog,
        accounts: vec![
            AccountMeta::new(dex, false),
            AccountMeta::new(mkt, false),
            AccountMeta::new(receipt, false),
            AccountMeta::new_readonly(lp, true),
            AccountMeta::new(lp_tok, false),
            AccountMeta::new_readonly(mint, false),
            AccountMeta::new(vault_pda, false),
            AccountMeta::new_readonly(tok_prog, false),
        ],
        data,
    }
}

fn ix_deposit_insurance(
    prog: Address, dex: Address, mkt: Address, receipt: Address, lp: Address,
    lp_tok: Address, mint: Address, vault_pda: Address, tok_prog: Address, amount: u64,
) -> Instruction {
    ix_deposit_insurance_ext(prog, dex, mkt, receipt, lp, lp_tok, mint, vault_pda, tok_prog, amount, false)
}

fn ix_withdraw_insurance(
    prog: Address, dex: Address, mkt: Address, receipt: Address, lp: Address,
    dest_tok: Address, mint: Address, vault_pda: Address, tok_prog: Address, burn_shares: u64,
) -> Instruction {
    let mut data = vec![0u8; 9];
    data[0] = 9;
    data[1..9].copy_from_slice(&burn_shares.to_le_bytes());
    Instruction {
        program_id: prog,
        accounts: vec![
            AccountMeta::new(dex, false),
            AccountMeta::new(mkt, false),
            AccountMeta::new(receipt, false),
            AccountMeta::new_readonly(lp, true),
            AccountMeta::new(dest_tok, false),
            AccountMeta::new_readonly(mint, false),
            AccountMeta::new(vault_pda, false),
            AccountMeta::new_readonly(tok_prog, false),
        ],
        data,
    }
}

fn ix_refresh_leg(prog: Address, dex: Address, mkt: Address, pfl: Address, force_haircut: bool) -> Instruction {
    Instruction {
        program_id: prog,
        accounts: vec![
            AccountMeta::new(dex, false),
            AccountMeta::new(mkt, false),
            AccountMeta::new(pfl, false),
        ],
        data: vec![10, if force_haircut { 1 } else { 0 }],
    }
}

fn ix_trade_ext(
    prog: Address, dex: Address, mkt: Address,
    pfl_l: Address, owner_l: Address, pfl_s: Address, owner_s: Address,
    mode: u8, qty: u64, exec_price: u64,
) -> Instruction {
    let mut data = vec![0u8; 18];
    data[0] = 11;
    data[1] = mode;
    data[2..10].copy_from_slice(&qty.to_le_bytes());
    data[10..18].copy_from_slice(&exec_price.to_le_bytes());
    Instruction {
        program_id: prog,
        accounts: vec![
            AccountMeta::new(dex, false),
            AccountMeta::new(mkt, false),
            AccountMeta::new(pfl_l, false),
            AccountMeta::new_readonly(owner_l, true),
            AccountMeta::new(pfl_s, false),
            AccountMeta::new_readonly(owner_s, true),
        ],
        data,
    }
}

fn ix_trade(
    prog: Address, dex: Address, mkt: Address,
    pfl_l: Address, owner_l: Address, pfl_s: Address, owner_s: Address,
    mode: u8, qty: u64,
) -> Instruction {
    ix_trade_ext(prog, dex, mkt, pfl_l, owner_l, pfl_s, owner_s, mode, qty, 0)
}

fn ix_liquidate(
    prog: Address, dex: Address, mkt: Address, pfl: Address,
    liq_tok: Address, mint: Address, vault_pda: Address, tok_prog: Address,
) -> Instruction {
    Instruction {
        program_id: prog,
        accounts: vec![
            AccountMeta::new(dex, false),
            AccountMeta::new(mkt, false),
            AccountMeta::new(pfl, false),
            AccountMeta::new(liq_tok, false),
            AccountMeta::new_readonly(mint, false),
            AccountMeta::new(vault_pda, false),
            AccountMeta::new_readonly(tok_prog, false),
        ],
        data: vec![12],
    }
}

fn ix_clear_dead_leg(prog: Address, dex: Address, mkt: Address, pfl: Address) -> Instruction {
    Instruction {
        program_id: prog,
        accounts: vec![
            AccountMeta::new(dex, false),
            AccountMeta::new(mkt, false),
            AccountMeta::new(pfl, false),
        ],
        data: vec![13],
    }
}

fn ix_start_wind_down(prog: Address, mkt: Address, caller: Address) -> Instruction {
    Instruction {
        program_id: prog,
        accounts: vec![AccountMeta::new(mkt, false), AccountMeta::new_readonly(caller, true)],
        data: vec![14],
    }
}

fn ix_force_close_pair(prog: Address, dex: Address, mkt: Address, pfl_l: Address, pfl_s: Address) -> Instruction {
    Instruction {
        program_id: prog,
        accounts: vec![
            AccountMeta::new(dex, false),
            AccountMeta::new(mkt, false),
            AccountMeta::new(pfl_l, false),
            AccountMeta::new(pfl_s, false),
        ],
        data: vec![15],
    }
}

fn ix_resolve_market(prog: Address, dex: Address, mkt: Address) -> Instruction {
    Instruction {
        program_id: prog,
        accounts: vec![AccountMeta::new(dex, false), AccountMeta::new(mkt, false)],
        data: vec![16],
    }
}

fn ix_claim_resolved(prog: Address, dex: Address, mkt: Address, pfl: Address) -> Instruction {
    Instruction {
        program_id: prog,
        accounts: vec![
            AccountMeta::new(dex, false),
            AccountMeta::new(mkt, false),
            AccountMeta::new(pfl, false),
        ],
        data: vec![17],
    }
}

fn ix_tombstone_market(prog: Address, mkt: Address) -> Instruction {
    Instruction {
        program_id: prog,
        accounts: vec![AccountMeta::new(mkt, false)],
        data: vec![18],
    }
}

/// Build `RefreshLeg` instructions for every active open leg of `pfl` in `markets_by_id`.
fn refresh_open_legs_ixs(
    svm: &LiteSVM,
    prog: Address,
    dex: Address,
    pfl: Address,
    markets: &[(u64, Address)],
) -> Vec<Instruction> {
    let mut ixs = Vec::new();
    for idx in 0..MAX_LEGS {
        let base = LEG_HEADER + idx * LEG_STRIDE;
        if read_u8(svm, &pfl, base) != 0 && read_u8(svm, &pfl, base + 1) != 0 {
            let mid = read_u64(svm, &pfl, base + 8);
            if let Some((_, mkt)) = markets.iter().find(|(id, _)| *id == mid) {
                ixs.push(ix_refresh_leg(prog, dex, *mkt, pfl, false));
            }
        }
    }
    ixs
}

/// Deterministic xorshift64 PRNG for reproducible 1,000-step stateful fuzzing.
struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }
    fn range(&mut self, n: u64) -> u64 {
        if n == 0 { 0 } else { self.next() % n }
    }
}

fn main() {
    let so_path = std::env::args()
        .nth(1)
        .unwrap_or_else(|| "build/percolator.so".to_string());
    let elf = std::fs::read(&so_path).unwrap_or_else(|e| panic!("Failed to read {}: {}", so_path, e));
    println!("==================================================================================");
    println!("  percolator-lean v2 — Realizable Shared Cross-Margin Perps DEX Verification Suite");
    println!("  Binary: {} ({} bytes, 0 heap, 0 engine/prog split)", so_path, elf.len());
    println!("==================================================================================");

    let mut svm = LiteSVM::new();
    let prog_id = Keypair::new().pubkey();
    svm.add_program(prog_id, &elf).expect("ELF load failed");
    set_slot(&mut svm, 100);

    let payer = Keypair::new();
    let dex_admin = Keypair::new();
    let alice = Keypair::new();
    let bob = Keypair::new();
    let lp = Keypair::new();
    let keeper = Keypair::new();
    let attacker = Keypair::new();
    let btc_oracle = Keypair::new();
    let eth_oracle = Keypair::new();
    let scam_oracle = Keypair::new();
    let adl_oracle = Keypair::new();
    let fake_tok_prog = Keypair::new().pubkey();
    // Load a REAL executable no-op sBPF program (returns Ok(0) on any CPI!) as `fake_tok_prog`!
    // If `checkDexVaultAndMint` / `checkTokenProg` error were ever dropped, DepositCollateral would
    // SUCCEED and mint phantom collateral; with the fix, every CPI entry MUST reject with Custom(120).
    let noop_elf = std::fs::read("../lean-svm/build/noop.so")
        .expect("Failed to read ../lean-svm/build/noop.so (run lean-svm build first)");
    svm.add_program(fake_tok_prog, &noop_elf).expect("noop ELF load failed");

    for kp in [&payer, &dex_admin, &alice, &bob, &lp, &keeper, &attacker, &btc_oracle, &eth_oracle, &scam_oracle, &adl_oracle] {
        svm.airdrop(&kp.pubkey(), 10_000_000_000).unwrap();
    }

    // Create USDC (6 decimals) quote mint
    let mint = Keypair::new().pubkey();
    svm.set_account(
        mint,
        Account {
            lamports: 10_000_000,
            data: make_spl_mint(6, 10_000_000_000_000, &dex_admin.pubkey()),
            owner: TOKEN_PROGRAM_ID,
            executable: false,
            rent_epoch: 0,
        },
    )
    .unwrap();

    let fee_vault = create_tok_acc(&mut svm, &mint, &dex_admin.pubkey(), 0);
    let alice_tok = create_tok_acc(&mut svm, &mint, &alice.pubkey(), 10_000_000_000);
    let bob_tok = create_tok_acc(&mut svm, &mint, &bob.pubkey(), 10_000_000_000);
    let lp_tok = create_tok_acc(&mut svm, &mint, &lp.pubkey(), 10_000_000_000);
    let keeper_tok = create_tok_acc(&mut svm, &mint, &keeper.pubkey(), 0);
    let attacker_tok = create_tok_acc(&mut svm, &mint, &attacker.pubkey(), 10_000_000_000);

    // =========================================================================
    // SUITE 1: Real On-Chain InitDex PDA Vault Creation (ZERO vault mocks!)
    //   Tests fake tokenProg, fake sysProg, wrong bump, AND 1-lamport pre-funding
    //   griefing resilience! `InitDex` allocates, assigns & InitializeAccount3's
    //   the real SPL Token vault PDA on-chain via CPI!
    // =========================================================================
    let dex = create_prog_acc(&mut svm, &prog_id, DEX_SIZE);
    let (dex_vault, dex_bump) = derive_dex_vault(&prog_id, &dex);

    // Pre-send 1 lamport to `dex_vault` to simulate an attacker trying to grief PDA creation!
    svm.set_account(
        dex_vault,
        Account { lamports: 1, data: vec![], owner: SYSTEM_PROGRAM_ID, executable: false, rent_epoch: 0 },
    )
    .unwrap();

    // 1a. Reject fake Token Program ID
    send_err(
        &mut svm,
        ix_init_dex(prog_id, dex, dex_admin.pubkey(), mint, dex_vault, fee_vault, fake_tok_prog, SYSTEM_PROGRAM_ID, dex_bump, 6, 1_000_000, SPL_TOKEN_RENT_MIN),
        &payer,
        &[&payer, &dex_admin],
        "InitDex with fake tokenProg",
    );
    // 1b. Reject fake System Program ID
    send_err(
        &mut svm,
        ix_init_dex(prog_id, dex, dex_admin.pubkey(), mint, dex_vault, fee_vault, TOKEN_PROGRAM_ID, fake_tok_prog, dex_bump, 6, 1_000_000, SPL_TOKEN_RENT_MIN),
        &payer,
        &[&payer, &dex_admin],
        "InitDex with fake sysProg",
    );
    // 1c. Reject wrong PDA bump
    send_err(
        &mut svm,
        ix_init_dex(prog_id, dex, dex_admin.pubkey(), mint, dex_vault, fee_vault, TOKEN_PROGRAM_ID, SYSTEM_PROGRAM_ID, dex_bump.wrapping_sub(1), 6, 1_000_000, SPL_TOKEN_RENT_MIN),
        &payer,
        &[&payer, &dex_admin],
        "InitDex with wrong PDA bump",
    );

    // 1d. InitDex creates the real SPL Token PDA vault on-chain despite 1-lamport pre-funding!
    let cu_init_dex = send_ok(
        &mut svm,
        ix_init_dex(prog_id, dex, dex_admin.pubkey(), mint, dex_vault, fee_vault, TOKEN_PROGRAM_ID, SYSTEM_PROGRAM_ID, dex_bump, 6, 1_000_000, SPL_TOKEN_RENT_MIN),
        &payer,
        &[&payer, &dex_admin],
    );
    let vault_acc = svm.get_account(&dex_vault).expect("DexVault PDA must exist on-chain!");
    assert_eq!(vault_acc.owner, TOKEN_PROGRAM_ID);
    assert_eq!(vault_acc.data.len(), 165);
    assert_eq!(vault_acc.lamports, SPL_TOKEN_RENT_MIN);
    assert_eq!(token_amount(&svm, &dex_vault), 0);
    assert_dex_invariants(&svm, &dex, &dex_vault, &[], &[], "post-initDex");
    println!("[PASS] Suite 1: Real On-Chain InitDex PDA Vault Creation + Anti-PreFund Griefing ({} CU)", cu_init_dex);

    // =========================================================================
    // SUITE 2: Permissionless Multi-Market Creation + Solvency Envelope
    // =========================================================================
    let btc_mkt = create_prog_acc(&mut svm, &prog_id, MKT_SIZE);
    let eth_mkt = create_prog_acc(&mut svm, &prog_id, MKT_SIZE);
    let scam_mkt = create_prog_acc(&mut svm, &prog_id, MKT_SIZE);
    let bad_mkt = create_prog_acc(&mut svm, &prog_id, MKT_SIZE);

    // Reject invalid solvency envelope (maxMove 500 + liqFee 100 > mmBps 500)
    send_err(
        &mut svm,
        ix_create_market(prog_id, dex, bad_mkt, mint, btc_oracle.pubkey(), alice.pubkey(), alice_tok, fee_vault,
            100 * POS_SCALE, 20, 50, 0, 1000, 500, 100, 0, 500, 2500, 1_000_000 * POS_SCALE),
        &payer,
        &[&payer, &alice],
        "CreateMarket violating solvency envelope",
    );

    let cu_create_mkt = send_ok(
        &mut svm,
        ix_create_market(prog_id, dex, btc_mkt, mint, btc_oracle.pubkey(), alice.pubkey(), alice_tok, fee_vault,
            100 * POS_SCALE, 20, 50, 0, 1000, 500, 100, 0, 400, 2500, 1_000_000 * POS_SCALE),
        &payer,
        &[&payer, &alice],
    );
    send_ok(
        &mut svm,
        ix_create_market(prog_id, dex, eth_mkt, mint, eth_oracle.pubkey(), bob.pubkey(), bob_tok, fee_vault,
            100 * POS_SCALE, 20, 50, 0, 1000, 500, 100, 0, 400, 2500, 1_000_000 * POS_SCALE),
        &payer,
        &[&payer, &bob],
    );
    send_ok(
        &mut svm,
        ix_create_market(prog_id, dex, scam_mkt, mint, scam_oracle.pubkey(), attacker.pubkey(), attacker_tok, fee_vault,
            100 * POS_SCALE, 20, 50, 0, 1000, 500, 100, 0, 400, 2500, 1_000_000 * POS_SCALE),
        &payer,
        &[&payer, &attacker],
    );
    assert_eq!(token_amount(&svm, &fee_vault), 3_000_000);

    // UpdateCreateFee affects ZERO markets/portfolios
    send_ok(&mut svm, ix_update_create_fee(prog_id, dex, dex_admin.pubkey(), 0, None), &payer, &[&payer, &dex_admin]);

    // Deposit isolated insurance to BTC ($1000), ETH ($500), SCAM ($100)
    let btc_ins = create_prog_acc(&mut svm, &prog_id, INS_SIZE);
    let eth_ins = create_prog_acc(&mut svm, &prog_id, INS_SIZE);
    let scam_ins = create_prog_acc(&mut svm, &prog_id, INS_SIZE);
    send_ok(&mut svm, ix_deposit_insurance(prog_id, dex, btc_mkt, btc_ins, lp.pubkey(), lp_tok, mint, dex_vault, TOKEN_PROGRAM_ID, 1_000 * POS_SCALE), &payer, &[&payer, &lp]);
    send_ok(&mut svm, ix_deposit_insurance(prog_id, dex, eth_mkt, eth_ins, lp.pubkey(), lp_tok, mint, dex_vault, TOKEN_PROGRAM_ID, 500 * POS_SCALE), &payer, &[&payer, &lp]);
    send_ok(&mut svm, ix_deposit_insurance(prog_id, dex, scam_mkt, scam_ins, lp.pubkey(), lp_tok, mint, dex_vault, TOKEN_PROGRAM_ID, 100 * POS_SCALE), &payer, &[&payer, &lp]);

    let all_mkts = vec![btc_mkt, eth_mkt, scam_mkt];
    assert_dex_invariants(&svm, &dex, &dex_vault, &all_mkts, &[], "post-markets");
    println!("[PASS] Suite 2: Multi-Market Creation + Solvency Envelope + Isolated Insurance ({} CU)", cu_create_mkt);

    // =========================================================================
    // SUITE 3: Hyperliquid Cross-Margin Capital Efficiency (Hedged Spread!)
    //   Alice puts up $100 shared capital, opens Long $500 BTC + Short $500 ETH
    //   (10x gross leverage, IM = $50 + $50 = $100).
    //   Both BTC & ETH drop ~7.84% over 2 slots -> atomic [RefreshLeg(ETH), RefreshLeg(BTC)]
    //   nets +$39.20 ETH profit directly against -$39.20 BTC loss -> $100 capital, 0 liquidation!
    // =========================================================================
    let alice_pfl = create_prog_acc(&mut svm, &prog_id, PFL_SIZE);
    let bob_pfl = create_prog_acc(&mut svm, &prog_id, PFL_SIZE);
    let attacker_pfl = create_prog_acc(&mut svm, &prog_id, PFL_SIZE);
    send_ok(&mut svm, ix_init_portfolio(prog_id, dex, alice_pfl, alice.pubkey()), &payer, &[&payer, &alice]);
    send_ok(&mut svm, ix_init_portfolio(prog_id, dex, bob_pfl, bob.pubkey()), &payer, &[&payer, &bob]);
    send_ok(&mut svm, ix_init_portfolio(prog_id, dex, attacker_pfl, attacker.pubkey()), &payer, &[&payer, &attacker]);
    let all_pfls = vec![alice_pfl, bob_pfl, attacker_pfl];

    let cu_dep = send_ok(&mut svm, ix_deposit_collateral(prog_id, dex, alice_pfl, alice.pubkey(), alice_tok, mint, dex_vault, TOKEN_PROGRAM_ID, 100 * POS_SCALE), &payer, &[&payer, &alice]);
    send_ok(&mut svm, ix_deposit_collateral(prog_id, dex, bob_pfl, bob.pubkey(), bob_tok, mint, dex_vault, TOKEN_PROGRAM_ID, 1_000 * POS_SCALE), &payer, &[&payer, &bob]);
    send_ok(&mut svm, ix_deposit_collateral(prog_id, dex, attacker_pfl, attacker.pubkey(), attacker_tok, mint, dex_vault, TOKEN_PROGRAM_ID, 500 * POS_SCALE), &payer, &[&payer, &attacker]);

    // Alice opens Long 5 BTC ($500) + Short 5 ETH ($500) on $100 capital!
    let cu_trade = send_ok(&mut svm, ix_trade(prog_id, dex, btc_mkt, alice_pfl, alice.pubkey(), bob_pfl, bob.pubkey(), 0, 5 * POS_SCALE), &payer, &[&payer, &alice, &bob]);
    send_ok(&mut svm, ix_trade(prog_id, dex, eth_mkt, bob_pfl, bob.pubkey(), alice_pfl, alice.pubkey(), 0, 5 * POS_SCALE), &payer, &[&payer, &bob, &alice]);
    assert_eq!(read_u64(&svm, &alice_pfl, 88), 100 * POS_SCALE);
    assert_eq!(read_u64(&svm, &alice_pfl, 104), 100 * POS_SCALE); // totalIm == $100!
    assert_eq!(read_u64(&svm, &alice_pfl, 96), 50 * POS_SCALE);   // totalMm == $50!
    assert_dex_invariants(&svm, &dex, &dex_vault, &all_mkts, &all_pfls, "post-spread-open");

    // Slot 101: Both BTC and ETH drop 4% ($100 -> $96)
    set_slot(&mut svm, 101);
    let cu_oracle = send_ok(&mut svm, ix_update_oracle(prog_id, btc_mkt, btc_oracle.pubkey(), 96 * POS_SCALE, 0, 0), &payer, &[&payer, &btc_oracle]);
    send_ok(&mut svm, ix_update_oracle(prog_id, eth_mkt, eth_oracle.pubkey(), 96 * POS_SCALE, 0, 0), &payer, &[&payer, &eth_oracle]);
    // Bob (ETH loser) refreshes ETH -> credits R_ETH += $20
    let cu_refresh = send_ok(&mut svm, ix_refresh_leg(prog_id, dex, eth_mkt, bob_pfl, false), &payer, &[&payer]);
    // Alice atomically runs [RefreshLeg(ETH), RefreshLeg(BTC)] in ONE tx!
    send_ixs_ok(
        &mut svm,
        &[
            ix_refresh_leg(prog_id, dex, eth_mkt, alice_pfl, false),
            ix_refresh_leg(prog_id, dex, btc_mkt, alice_pfl, false),
        ],
        &payer,
        &[&payer],
    );
    assert_eq!(read_u64(&svm, &alice_pfl, 88), 100 * POS_SCALE, "Alice hedged spread capital must remain EXACTLY $100!");
    send_err(&mut svm, ix_liquidate(prog_id, dex, btc_mkt, alice_pfl, keeper_tok, mint, dex_vault, TOKEN_PROGRAM_ID), &payer, &[&payer], "Healthy hedged Alice cannot be liquidated");

    // Slot 102: Both BTC and ETH drop another 4% ($96 -> $92.16)
    set_slot(&mut svm, 102);
    send_ok(&mut svm, ix_update_oracle(prog_id, btc_mkt, btc_oracle.pubkey(), 92_160_000, 0, 0), &payer, &[&payer, &btc_oracle]);
    send_ok(&mut svm, ix_update_oracle(prog_id, eth_mkt, eth_oracle.pubkey(), 92_160_000, 0, 0), &payer, &[&payer, &eth_oracle]);
    send_ok(&mut svm, ix_refresh_leg(prog_id, dex, eth_mkt, bob_pfl, false), &payer, &[&payer]);
    send_ixs_ok(
        &mut svm,
        &[
            ix_refresh_leg(prog_id, dex, eth_mkt, alice_pfl, false),
            ix_refresh_leg(prog_id, dex, btc_mkt, alice_pfl, false),
        ],
        &payer,
        &[&payer],
    );
    assert_eq!(read_u64(&svm, &alice_pfl, 88), 100 * POS_SCALE, "Alice hedged spread survives 7.84% drop with $100 capital!");

    // Verify same-slot freshness on WithdrawCollateral!
    set_slot(&mut svm, 103);
    send_err(
        &mut svm,
        ix_withdraw_collateral(prog_id, dex, alice_pfl, alice.pubkey(), alice_tok, mint, dex_vault, TOKEN_PROGRAM_ID, 5 * POS_SCALE),
        &payer,
        &[&payer, &alice],
        "WithdrawCollateral with stale legs must fail",
    );
    // Atomic [RefreshLeg(BTC), RefreshLeg(ETH), WithdrawCollateral($5)] SUCCEEDS!
    let cu_wdr = send_ixs_ok(
        &mut svm,
        &[
            ix_refresh_leg(prog_id, dex, btc_mkt, alice_pfl, false),
            ix_refresh_leg(prog_id, dex, eth_mkt, alice_pfl, false),
            ix_withdraw_collateral(prog_id, dex, alice_pfl, alice.pubkey(), alice_tok, mint, dex_vault, TOKEN_PROGRAM_ID, 5 * POS_SCALE),
        ],
        &payer,
        &[&payer, &alice],
    );
    assert_eq!(read_u64(&svm, &alice_pfl, 88), 95 * POS_SCALE);
    assert_dex_invariants(&svm, &dex, &dex_vault, &all_mkts, &all_pfls, "post-hyperliquid-spread");
    println!(
        "[PASS] Suite 3: Hyperliquid Hedged Spread + Same-Slot Freshness (dep={} CU, trade={} CU, oracle={} CU, refresh={} CU, atomic-wdr={} CU)",
        cu_dep, cu_trade, cu_oracle, cu_refresh, cu_wdr
    );

    // =========================================================================
    // SUITE 4: Anti-Reverse-Contagion + Fake-PnL Isolation!
    //   Alice closes ETH, adds $15 so capital = $110, holds Long 5 BTC (MM=$23.04)
    //   and opens Short 2 SCAM ($200 notional, MM=$10, IM=$20) vs Attacker.
    //   Attacker pumps SCAM +4% for 15 consecutive slots ($100 -> $180+)!
    //   Keeper liquidates Alice's SCAM leg:
    //   - SCAM loss + liqFee NEVER touches Alice's BTC MM ($23.04)!
    //   - After SCAM liquidation, Alice's BTC leg is STILL 100% HEALTHY!
    //   - I_BTC and I_ETH are BIT-FOR-BIT UNCHANGED!
    // =========================================================================
    // Close Alice's ETH leg cleanly so Alice has Long 5 BTC only
    send_ok(&mut svm, ix_trade(prog_id, dex, eth_mkt, bob_pfl, bob.pubkey(), alice_pfl, alice.pubkey(), 1, 5 * POS_SCALE), &payer, &[&payer, &bob, &alice]);
    // Also refresh Bob's BTC leg so Bob collects his BTC profit cleanly
    send_ok(&mut svm, ix_refresh_leg(prog_id, dex, btc_mkt, bob_pfl, false), &payer, &[&payer]);
    // Alice opens Short 2 SCAM ($200) against Attacker (Long 2 SCAM)
    send_ok(&mut svm, ix_trade(prog_id, dex, scam_mkt, attacker_pfl, attacker.pubkey(), alice_pfl, alice.pubkey(), 0, 2 * POS_SCALE), &payer, &[&payer, &attacker, &alice]);

    let btc_ins_before = read_u64(&svm, &btc_mkt, 224);
    let eth_ins_before = read_u64(&svm, &eth_mkt, 224);
    let alice_btc_mm = read_u64(&svm, &alice_pfl, LEG_HEADER + 72); // slot 0 = BTC leg!
    assert!(alice_btc_mm >= 23_000_000, "Alice BTC MM expected ~$23.04, got {}", alice_btc_mm);

    // Attacker pumps SCAM +4% per slot for 15 slots ($100 -> ~$180.09, loss ~$160 > Alice's $95 capital!)
    let mut scam_p = 100 * POS_SCALE;
    for step in 1..=15 {
        set_slot(&mut svm, 103 + step);
        scam_p = (scam_p * 104) / 100;
        send_ok(&mut svm, ix_update_oracle(prog_id, scam_mkt, scam_oracle.pubkey(), scam_p, 0, 0), &payer, &[&payer, &scam_oracle]);
    }
    // A1 Fix verification: bare Liquidate(SCAM) while Alice's BTC leg is stale MUST fail!
    send_err(
        &mut svm,
        ix_liquidate(prog_id, dex, scam_mkt, alice_pfl, keeper_tok, mint, dex_vault, TOKEN_PROGRAM_ID),
        &payer,
        &[&payer],
        "Bare Liquidate with stale BTC leg must be rejected (A1)",
    );
    // Keeper atomically refreshes Alice's BTC leg + liquidates Alice's blown-up SCAM leg!
    let cu_liq = send_ixs_ok(
        &mut svm,
        &[
            ix_refresh_leg(prog_id, dex, btc_mkt, alice_pfl, false),
            ix_liquidate(prog_id, dex, scam_mkt, alice_pfl, keeper_tok, mint, dex_vault, TOKEN_PROGRAM_ID),
        ],
        &payer,
        &[&payer],
    );
    let alice_cap_after = read_u64(&svm, &alice_pfl, 88);
    let alice_mm_after = read_u64(&svm, &alice_pfl, 96);
    assert!(
        alice_cap_after >= alice_btc_mm && alice_cap_after >= alice_mm_after,
        "ANTI-REVERSE-CONTAGION VIOLATED: Alice capital ({}) < BTC MM ({})!",
        alice_cap_after, alice_mm_after
    );
    assert_eq!(read_u64(&svm, &btc_mkt, 224), btc_ins_before, "I_BTC must be bit-for-bit untouched!");
    assert_eq!(read_u64(&svm, &eth_mkt, 224), eth_ins_before, "I_ETH must be bit-for-bit untouched!");

    // Verify Alice's BTC leg is STILL healthy and cannot be liquidated!
    set_slot(&mut svm, 119);
    send_ok(&mut svm, ix_update_oracle(prog_id, btc_mkt, btc_oracle.pubkey(), 92_160_000, 0, 0), &payer, &[&payer, &btc_oracle]);
    send_err(&mut svm, ix_liquidate(prog_id, dex, btc_mkt, alice_pfl, keeper_tok, mint, dex_vault, TOKEN_PROGRAM_ID), &payer, &[&payer], "Alice BTC leg must survive SCAM explosion!");

    // Attacker tries to claim fake paper profits on SCAM via ClearDeadLeg + RefreshLeg(forceHaircut=true)
    // Attacker's extraction is strictly bounded by R_SCAM (Alice's seized SCAM margin + capped 25% of I_SCAM)!
    let scam_r_before = read_u64(&svm, &scam_mkt, 216);
    let attacker_cap_before = read_u64(&svm, &attacker_pfl, 88);
    send_ok(&mut svm, ix_clear_dead_leg(prog_id, dex, scam_mkt, attacker_pfl), &payer, &[&payer]);
    send_ok(&mut svm, ix_refresh_leg(prog_id, dex, scam_mkt, attacker_pfl, true), &payer, &[&payer]);
    let attacker_gain = read_u64(&svm, &attacker_pfl, 88) - attacker_cap_before;
    assert!(attacker_gain <= scam_r_before, "Attacker extracted {} > R_SCAM ({})!", attacker_gain, scam_r_before);
    assert_eq!(read_u64(&svm, &btc_mkt, 224), btc_ins_before, "I_BTC still untouched after Attacker claim!");
    assert_dex_invariants(&svm, &dex, &dex_vault, &all_mkts, &all_pfls, "post-scam-containment");

    // 4B: God-Mode RUG/USD Oracle Shielding Attacks (Alice + Mule vs Bob on SOL/USD!)
    //     Tests BOTH Long-RUG 12x pump AND Short-RUG 12x pump shielding attempts:
    //     Alice + Mule control RUG's oracle & inflate rugLeg.cachedMm >> Alice.capital;
    //     verify reservedMm firewall guarantees Bob receives 100.00% of his SOL/USD profit,
    //     ZERO haircut on Bob, and I_SOL bit-for-bit untouched!
    {
        let s_dex = create_prog_acc(&mut svm, &prog_id, DEX_SIZE);
        let (s_vault, s_bump) = derive_dex_vault(&prog_id, &s_dex);
        send_ok(&mut svm, ix_init_dex(prog_id, s_dex, dex_admin.pubkey(), mint, s_vault, fee_vault, TOKEN_PROGRAM_ID, SYSTEM_PROGRAM_ID, s_bump, 6, 0, SPL_TOKEN_RENT_MIN), &payer, &[&payer, &dex_admin]);
        let sol_orac = Keypair::new();
        let rug_orac = Keypair::new();
        let sol_mkt = create_prog_acc(&mut svm, &prog_id, MKT_SIZE);
        let rug_mkt = create_prog_acc(&mut svm, &prog_id, MKT_SIZE);
        let sol_ins = create_prog_acc(&mut svm, &prog_id, INS_SIZE);
        send_ok(&mut svm, ix_create_market(prog_id, s_dex, sol_mkt, mint, sol_orac.pubkey(), lp.pubkey(), lp_tok, fee_vault, 100 * POS_SCALE, 20, 200, 0, 1000, 500, 100, 0, 400, 2500, 1_000_000 * POS_SCALE), &payer, &[&payer, &lp]);
        send_ok(&mut svm, ix_create_market(prog_id, s_dex, rug_mkt, mint, rug_orac.pubkey(), attacker.pubkey(), attacker_tok, fee_vault, POS_SCALE, 20, 200, 0, 1000, 500, 100, 0, 400, 2500, 1_000_000 * POS_SCALE), &payer, &[&payer, &attacker]);
        send_ok(&mut svm, ix_deposit_insurance(prog_id, s_dex, sol_mkt, sol_ins, lp.pubkey(), lp_tok, mint, s_vault, TOKEN_PROGRAM_ID, 500 * POS_SCALE), &payer, &[&payer, &lp]);

        // 4B-1: Long-RUG 12x Pump Shielding Attack
        let a1 = Keypair::new(); let b1 = Keypair::new(); let m1 = Keypair::new();
        let a1_tok = create_tok_acc(&mut svm, &mint, &a1.pubkey(), 1_000 * POS_SCALE);
        let b1_tok = create_tok_acc(&mut svm, &mint, &b1.pubkey(), 1_000 * POS_SCALE);
        let m1_tok = create_tok_acc(&mut svm, &mint, &m1.pubkey(), 1_000 * POS_SCALE);
        let a1_pfl = create_prog_acc(&mut svm, &prog_id, PFL_SIZE);
        let b1_pfl = create_prog_acc(&mut svm, &prog_id, PFL_SIZE);
        let m1_pfl = create_prog_acc(&mut svm, &prog_id, PFL_SIZE);
        for (p, u, t, amt) in [
            (a1_pfl, &a1, a1_tok, 120 * POS_SCALE),
            (b1_pfl, &b1, b1_tok, 500 * POS_SCALE),
            (m1_pfl, &m1, m1_tok, 20 * POS_SCALE),
        ] {
            send_ok(&mut svm, ix_init_portfolio(prog_id, s_dex, p, u.pubkey()), &payer, &[&payer, u]);
            send_ok(&mut svm, ix_deposit_collateral(prog_id, s_dex, p, u.pubkey(), t, mint, s_vault, TOKEN_PROGRAM_ID, amt), &payer, &[&payer, u]);
        }
        // Alice1: Long 10 SOL ($1000, MM=$50, IM=$100) vs Bob1 + Long 200 RUG ($200, MM=$10, IM=$20) vs Mule1
        send_ok(&mut svm, ix_trade(prog_id, s_dex, sol_mkt, a1_pfl, a1.pubkey(), b1_pfl, b1.pubkey(), 0, 10 * POS_SCALE), &payer, &[&payer, &a1, &b1]);
        send_ok(&mut svm, ix_trade(prog_id, s_dex, rug_mkt, a1_pfl, a1.pubkey(), m1_pfl, m1.pubkey(), 0, 200 * POS_SCALE), &payer, &[&payer, &a1, &m1]);

        // 4B-2: Short-RUG 12x Pump Shielding Attack (simultaneously on same markets!)
        let a2 = Keypair::new(); let b2 = Keypair::new(); let m2 = Keypair::new();
        let a2_tok = create_tok_acc(&mut svm, &mint, &a2.pubkey(), 1_000 * POS_SCALE);
        let b2_tok = create_tok_acc(&mut svm, &mint, &b2.pubkey(), 1_000 * POS_SCALE);
        let m2_tok = create_tok_acc(&mut svm, &mint, &m2.pubkey(), 1_000 * POS_SCALE);
        let a2_pfl = create_prog_acc(&mut svm, &prog_id, PFL_SIZE);
        let b2_pfl = create_prog_acc(&mut svm, &prog_id, PFL_SIZE);
        let m2_pfl = create_prog_acc(&mut svm, &prog_id, PFL_SIZE);
        for (p, u, t, amt) in [
            (a2_pfl, &a2, a2_tok, 120 * POS_SCALE),
            (b2_pfl, &b2, b2_tok, 500 * POS_SCALE),
            (m2_pfl, &m2, m2_tok, 20 * POS_SCALE),
        ] {
            send_ok(&mut svm, ix_init_portfolio(prog_id, s_dex, p, u.pubkey()), &payer, &[&payer, u]);
            send_ok(&mut svm, ix_deposit_collateral(prog_id, s_dex, p, u.pubkey(), t, mint, s_vault, TOKEN_PROGRAM_ID, amt), &payer, &[&payer, u]);
        }
        send_ok(&mut svm, ix_trade(prog_id, s_dex, sol_mkt, a2_pfl, a2.pubkey(), b2_pfl, b2.pubkey(), 0, 10 * POS_SCALE), &payer, &[&payer, &a2, &b2]);
        send_ok(&mut svm, ix_trade(prog_id, s_dex, rug_mkt, m2_pfl, m2.pubkey(), a2_pfl, a2.pubkey(), 0, 200 * POS_SCALE), &payer, &[&payer, &m2, &a2]);

        let s_mkts = vec![sol_mkt, rug_mkt];
        let s_pfls = vec![a1_pfl, b1_pfl, m1_pfl, a2_pfl, b2_pfl, m2_pfl];

        // Alice + Mule pump RUG/USD +4%/slot for 65 slots ($1 -> >$12.50, >12x!)
        // WITHOUT refreshing on intermediate slots (direct 12x jump in cachedMm on slot +65!)
        let base_sl = get_slot(&svm);
        let mut rug_p = POS_SCALE;
        for step in 1..=65u64 {
            set_slot(&mut svm, base_sl + step);
            rug_p = (rug_p * 104) / 100;
            send_ok(&mut svm, ix_update_oracle(prog_id, rug_mkt, rug_orac.pubkey(), rug_p, 0, 0), &payer, &[&payer, &rug_orac]);
        }
        // Refresh RUG on both Alice1 (Long RUG) and Alice2 (Short RUG): cachedMm_RUG > $120!
        send_ok(&mut svm, ix_refresh_leg(prog_id, s_dex, rug_mkt, a1_pfl, false), &payer, &[&payer]);
        send_ok(&mut svm, ix_refresh_leg(prog_id, s_dex, rug_mkt, a2_pfl, false), &payer, &[&payer]);
        let a1_rug_mm = read_u64(&svm, &a1_pfl, LEG_HEADER + LEG_STRIDE + 72);
        let a2_rug_mm = read_u64(&svm, &a2_pfl, LEG_HEADER + LEG_STRIDE + 72);
        assert!(a1_rug_mm > 120 * POS_SCALE && a2_rug_mm > 120 * POS_SCALE, "RUG cachedMm must exceed Alice's $120 capital!");
        // Anti-shielding check: Alice1 & Alice2's SOL reservedMm MUST still be exact $50!
        assert_eq!(read_u64(&svm, &a1_pfl, LEG_HEADER + 96), 50 * POS_SCALE, "Alice1 SOL reservedMm protected!");
        assert_eq!(read_u64(&svm, &a2_pfl, LEG_HEADER + 96), 50 * POS_SCALE, "Alice2 SOL reservedMm protected!");
        assert_eq!(read_u64(&svm, &a2_pfl, 88), 50 * POS_SCALE, "Alice2 capital stopped at exact SOL MM=$50!");
        assert_eq!(read_u64(&svm, &a2_pfl, LEG_HEADER + LEG_STRIDE + 96), 0, "Alice2 RUG reservedMm capped at $0!");
        assert_dex_invariants(&svm, &s_dex, &s_vault, &s_mkts, &s_pfls, "4B-post-rug-12x-pump");

        // Now SOL/USD drops -4% ($100 -> $96: each Alice loses $40, each Bob earns +$40)!
        set_slot(&mut svm, base_sl + 66);
        send_ok(&mut svm, ix_update_oracle(prog_id, sol_mkt, sol_orac.pubkey(), 96 * POS_SCALE, 0, 0), &payer, &[&payer, &sol_orac]);
        let sol_ins_before = read_u64(&svm, &sol_mkt, 224);
        send_ixs_ok(&mut svm, &[
            ix_refresh_leg(prog_id, s_dex, rug_mkt, a1_pfl, false),
            ix_liquidate(prog_id, s_dex, sol_mkt, a1_pfl, keeper_tok, mint, s_vault, TOKEN_PROGRAM_ID),
        ], &payer, &[&payer]);
        send_ixs_ok(&mut svm, &[
            ix_refresh_leg(prog_id, s_dex, rug_mkt, a2_pfl, false),
            ix_liquidate(prog_id, s_dex, sol_mkt, a2_pfl, keeper_tok, mint, s_vault, TOKEN_PROGRAM_ID),
        ], &payer, &[&payer]);
        // I_SOL MUST be bit-for-bit untouched (ZERO shortfall on BOTH Alice1 and Alice2)!
        assert_eq!(read_u64(&svm, &sol_mkt, 224), sol_ins_before, "I_SOL MUST be bit-for-bit untouched!");
        // Both Bob1 and Bob2 collect 100.00% (+$40.00 each!) directly into their capital — ZERO haircut!
        send_ok(&mut svm, ix_refresh_leg(prog_id, s_dex, sol_mkt, b1_pfl, false), &payer, &[&payer]);
        send_ok(&mut svm, ix_refresh_leg(prog_id, s_dex, sol_mkt, b2_pfl, false), &payer, &[&payer]);
        assert_eq!(read_u64(&svm, &b1_pfl, 88), 540 * POS_SCALE, "Bob1 received 100.00% (+$40) despite Long-RUG 12x shielding attack!");
        assert_eq!(read_u64(&svm, &b2_pfl, 88), 540 * POS_SCALE, "Bob2 received 100.00% (+$40) despite Short-RUG 12x shielding attack!");
        assert_dex_invariants(&svm, &s_dex, &s_vault, &s_mkts, &s_pfls, "4B-post-bob-100pct-payout");
    }
    // Restore clock slot to 119 for Suite 5 (4B used isolated s_dex)
    set_slot(&mut svm, 119);
    println!(
        "[PASS] Suite 4: Anti-Reverse-Contagion + God-Mode RUG 12x Shielding Immunity (liq={} CU, Alice survived cap={} >= BTC_MM={}, Bob1/Bob2 paid 100% +$40, I_SOL untouched!)",
        cu_liq, alice_cap_after, alice_mm_after
    );

    // =========================================================================
    // SUITE 5: Security Regression Tests (All 5 Hardened Attack Vectors)
    // =========================================================================
    // 5a. Same-slot UpdateOracle spam rejected (slot 119 already updated BTC!)
    send_err(&mut svm, ix_update_oracle(prog_id, btc_mkt, btc_oracle.pubkey(), 93_000_000, 0, 0), &payer, &[&payer, &btc_oracle], "Same-slot UpdateOracle spam");
    // 5b. Unclamped oracle jump rejected (+10% > 4%)
    set_slot(&mut svm, 120);
    send_err(&mut svm, ix_update_oracle(prog_id, btc_mkt, btc_oracle.pubkey(), 102_000_000, 0, 0), &payer, &[&payer, &btc_oracle], "Unclamped oracle jump");
    // 5c. Real executable noop.so TokenProg + wrong mint + wrong vault MUST fail with exact PErr codes!
    //     (Regression test for Bug A0: executable fake token program returning Ok(0) on CPI!)
    let fake_mint = Keypair::new().pubkey();
    let fake_vault = create_tok_acc(&mut svm, &mint, &attacker.pubkey(), 0);
    let alice_cap_before_a0 = read_u64(&svm, &alice_pfl, 88);
    send_err_custom(&mut svm, ix_deposit_collateral(prog_id, dex, alice_pfl, alice.pubkey(), alice_tok, mint, dex_vault, fake_tok_prog, 1_000_000_000), &payer, &[&payer, &alice], 120, "Deposit with real executable noop.so tokenProg");
    assert_eq!(read_u64(&svm, &alice_pfl, 88), alice_cap_before_a0, "Phantom collateral minted via noop.so!");
    send_err_custom(&mut svm, ix_deposit_collateral(prog_id, dex, alice_pfl, alice.pubkey(), alice_tok, fake_mint, dex_vault, TOKEN_PROGRAM_ID, 1_000), &payer, &[&payer, &alice], 112, "Deposit with wrong mint");
    send_err_custom(&mut svm, ix_deposit_collateral(prog_id, dex, alice_pfl, alice.pubkey(), alice_tok, mint, fake_vault, TOKEN_PROGRAM_ID, 1_000), &payer, &[&payer, &alice], 113, "Deposit with wrong vaultPda");
    send_err_custom(&mut svm, ix_withdraw_collateral(prog_id, dex, bob_pfl, bob.pubkey(), bob_tok, mint, dex_vault, fake_tok_prog, 1000), &payer, &[&payer, &bob], 120, "Withdraw with real executable noop.so tokenProg");
    send_err_custom(&mut svm, ix_withdraw_collateral(prog_id, dex, bob_pfl, bob.pubkey(), bob_tok, fake_mint, dex_vault, TOKEN_PROGRAM_ID, 1000), &payer, &[&payer, &bob], 112, "Withdraw with wrong mint");
    send_err_custom(&mut svm, ix_withdraw_collateral(prog_id, dex, bob_pfl, bob.pubkey(), bob_tok, mint, fake_vault, TOKEN_PROGRAM_ID, 1000), &payer, &[&payer, &bob], 113, "Withdraw with wrong vaultPda");
    send_err_custom(&mut svm, ix_deposit_insurance(prog_id, dex, btc_mkt, btc_ins, lp.pubkey(), lp_tok, mint, dex_vault, fake_tok_prog, 1000), &payer, &[&payer, &lp], 120, "DepositInsurance with real executable noop.so tokenProg");
    send_err_custom(&mut svm, ix_withdraw_insurance(prog_id, dex, btc_mkt, btc_ins, lp.pubkey(), lp_tok, mint, dex_vault, fake_tok_prog, 1000), &payer, &[&payer, &lp], 120, "WithdrawInsurance with real executable noop.so tokenProg");
    send_err_custom(&mut svm, ix_liquidate(prog_id, dex, btc_mkt, alice_pfl, keeper_tok, mint, dex_vault, fake_tok_prog), &payer, &[&payer], 120, "Liquidate with real executable noop.so tokenProg");
    // 5d. Aliased Trade rejected
    send_err(&mut svm, ix_trade(prog_id, dex, eth_mkt, bob_pfl, bob.pubkey(), bob_pfl, bob.pubkey(), 0, POS_SCALE), &payer, &[&payer, &bob], "Aliased Trade");
    // 5e. WithdrawInsurance while OI > 0 rejected (BTC still has 5 OI!)
    send_err(&mut svm, ix_withdraw_insurance(prog_id, dex, btc_mkt, btc_ins, lp.pubkey(), lp_tok, mint, dex_vault, TOKEN_PROGRAM_ID, 1000), &payer, &[&payer, &lp], "WithdrawInsurance with OI > 0");
    println!("[PASS] Suite 5: All 5 Runtime Security Regression Tests Rejected Cleanly!");

    // =========================================================================
    // SUITE 6: Post-ADL ClearDeadLeg + Full WindDown -> ForceClosePair ->
    //          ResolveMarket -> ClaimResolved -> WithdrawInsurance -> Tombstone!
    // =========================================================================
    let adl_mkt = create_prog_acc(&mut svm, &prog_id, MKT_SIZE);
    let adl_ins = create_prog_acc(&mut svm, &prog_id, INS_SIZE);
    send_ok(
        &mut svm,
        ix_create_market(prog_id, dex, adl_mkt, mint, adl_oracle.pubkey(), lp.pubkey(), lp_tok, fee_vault,
            100 * POS_SCALE, 10, 20, 0, 1000, 500, 100, 0, 400, 2500, 1_000_000 * POS_SCALE),
        &payer,
        &[&payer, &lp],
    );
    send_ok(&mut svm, ix_deposit_insurance(prog_id, dex, adl_mkt, adl_ins, lp.pubkey(), lp_tok, mint, dex_vault, TOKEN_PROGRAM_ID, 200 * POS_SCALE), &payer, &[&payer, &lp]);

    let t1 = Keypair::new();
    let t2 = Keypair::new();
    svm.airdrop(&t1.pubkey(), 10_000_000_000).unwrap();
    svm.airdrop(&t2.pubkey(), 10_000_000_000).unwrap();
    let t1_tok = create_tok_acc(&mut svm, &mint, &t1.pubkey(), 1_000 * POS_SCALE);
    let t2_tok = create_tok_acc(&mut svm, &mint, &t2.pubkey(), 1_000 * POS_SCALE);
    let t1_pfl = create_prog_acc(&mut svm, &prog_id, PFL_SIZE);
    let t2_pfl = create_prog_acc(&mut svm, &prog_id, PFL_SIZE);
    send_ok(&mut svm, ix_init_portfolio(prog_id, dex, t1_pfl, t1.pubkey()), &payer, &[&payer, &t1]);
    send_ok(&mut svm, ix_init_portfolio(prog_id, dex, t2_pfl, t2.pubkey()), &payer, &[&payer, &t2]);
    send_ok(&mut svm, ix_deposit_collateral(prog_id, dex, t1_pfl, t1.pubkey(), t1_tok, mint, dex_vault, TOKEN_PROGRAM_ID, 15 * POS_SCALE), &payer, &[&payer, &t1]);
    send_ok(&mut svm, ix_deposit_collateral(prog_id, dex, t2_pfl, t2.pubkey(), t2_tok, mint, dex_vault, TOKEN_PROGRAM_ID, 500 * POS_SCALE), &payer, &[&payer, &t2]);

    // T1 (Long 1 @ $100, cap=$15) vs T2 (Short 1 @ $100)
    send_ok(&mut svm, ix_trade(prog_id, dex, adl_mkt, t1_pfl, t1.pubkey(), t2_pfl, t2.pubkey(), 0, POS_SCALE), &payer, &[&payer, &t1, &t2]);
    // Crash price over 4 slots so T1 drops below MM and gets liquidated!
    let mut ap = 100 * POS_SCALE;
    for step in 1..=4 {
        set_slot(&mut svm, 120 + step);
        ap = (ap * 96) / 100;
        send_ok(&mut svm, ix_update_oracle(prog_id, adl_mkt, adl_oracle.pubkey(), ap, 0, 0), &payer, &[&payer, &adl_oracle]);
    }
    send_ok_assert_log(&mut svm, ix_liquidate(prog_id, dex, adl_mkt, t1_pfl, keeper_tok, mint, dex_vault, TOKEN_PROGRAM_ID), &payer, &[&payer], "Program log: 0x3,");
    assert_eq!(read_u64(&svm, &adl_mkt, 256), 0); // oiLong == 0
    assert_eq!(read_u64(&svm, &adl_mkt, 280), POS_SCALE); // rawBasisShort == 1.0 (dead leg!)
    // WithdrawInsurance MUST fail while dead leg rawBasis > 0!
    send_err(&mut svm, ix_withdraw_insurance(prog_id, dex, adl_mkt, adl_ins, lp.pubkey(), lp_tok, mint, dex_vault, TOKEN_PROGRAM_ID, 200 * POS_SCALE), &payer, &[&payer, &lp], "WithdrawInsurance while dead rawBasis > 0");
    // ClearDeadLeg resets rawBasisShort -> 0 AND adlShort -> ADL_ONE!
    let cu_clear = send_ok(&mut svm, ix_clear_dead_leg(prog_id, dex, adl_mkt, t2_pfl), &payer, &[&payer]);
    assert_eq!(read_u64(&svm, &adl_mkt, 280), 0);
    assert_eq!(read_u64(&svm, &adl_mkt, 296), ADL_ONE);

    // Market recovered! Re-open a fresh pair (T1 adds collateral, opens Long 1 vs T2 Short 1),
    // then burn admin, go stale -> permissionless WindDown -> ForceClosePair -> Resolve -> WithdrawIns -> Tombstone!
    send_ok_assert_log(&mut svm, ix_deposit_collateral(prog_id, dex, t1_pfl, t1.pubkey(), t1_tok, mint, dex_vault, TOKEN_PROGRAM_ID, 50 * POS_SCALE), &payer, &[&payer, &t1], "Program log: 0x4,");
    send_ok(&mut svm, ix_trade(prog_id, dex, adl_mkt, t1_pfl, t1.pubkey(), t2_pfl, t2.pubkey(), 0, POS_SCALE), &payer, &[&payer, &t1, &t2]);
    send_ok(&mut svm, ix_burn_market_admin(prog_id, adl_mkt, lp.pubkey()), &payer, &[&payer, &lp]);
    send_err(&mut svm, ix_start_wind_down(prog_id, adl_mkt, keeper.pubkey()), &payer, &[&payer, &keeper], "StartWindDown while oracle fresh");

    // Advance slot past maxStaleness (20) -> permissionless WindDown!
    set_slot(&mut svm, 150);
    send_ok(&mut svm, ix_start_wind_down(prog_id, adl_mkt, keeper.pubkey()), &payer, &[&payer, &keeper]);
    send_err(&mut svm, ix_force_close_pair(prog_id, dex, adl_mkt, t1_pfl, t2_pfl), &payer, &[&payer], "ForceClosePair during exitWindow");
    // Advance past exitWindow (10) -> permissionless ForceClosePair!
    set_slot(&mut svm, 160);
    send_ok_assert_log(&mut svm, ix_force_close_pair(prog_id, dex, adl_mkt, t1_pfl, t2_pfl), &payer, &[&payer], "Program log: 0x6,");
    send_ok_assert_log(&mut svm, ix_resolve_market(prog_id, dex, adl_mkt), &payer, &[&payer], "Program log: 0x7,");
    // If T2 still has any unclaimed posPnl leg on adl_mkt, claim it!
    let _ = send_ixs_try(&mut svm, &[ix_claim_resolved(prog_id, dex, adl_mkt, t2_pfl)], &payer, &[&payer]);
    send_ok(&mut svm, ix_withdraw_insurance(prog_id, dex, adl_mkt, adl_ins, lp.pubkey(), lp_tok, mint, dex_vault, TOKEN_PROGRAM_ID, 200 * POS_SCALE), &payer, &[&payer, &lp]);
    send_ok(&mut svm, ix_tombstone_market(prog_id, adl_mkt), &payer, &[&payer]);
    assert_eq!(read_u8(&svm, &adl_mkt, 4), 3); // STATUS_TOMBSTONED
    send_err(&mut svm, ix_burn_market_admin(prog_id, adl_mkt, lp.pubkey()), &payer, &[&payer, &lp], "BurnAdmin on tombstoned market");

    // Test CloseAccount rent reclaim on empty InsReceipt, empty Portfolio, and Tombstoned Market!
    // 6a. Reject closing non-empty Portfolio (t1_pfl still has capital > 0!)
    send_err(&mut svm, ix_close_account(prog_id, t1_pfl, t1.pubkey(), keeper.pubkey()), &payer, &[&payer, &t1], "Close non-empty Portfolio");
    // 6b. Empty t1_pfl (withdraw remaining capital) and close it + reclaim rent!
    let t1_rem = read_u64(&svm, &t1_pfl, 88);
    if t1_rem > 0 {
        send_ok_assert_log(&mut svm, ix_withdraw_collateral(prog_id, dex, t1_pfl, t1.pubkey(), t1_tok, mint, dex_vault, TOKEN_PROGRAM_ID, t1_rem), &payer, &[&payer, &t1], "Program log: 0x5,");
    }
    let keeper_lam_0 = svm.get_account(&keeper.pubkey()).unwrap().lamports;
    let cu_close = send_ok(&mut svm, ix_close_account(prog_id, t1_pfl, t1.pubkey(), keeper.pubkey()), &payer, &[&payer, &t1]);
    assert_eq!(svm.get_account(&t1_pfl).map(|a| a.lamports).unwrap_or(0), 0);
    // Close empty adl_ins receipt (0 shares) & Tombstoned adl_mkt (burned admin -> permissionless)!
    send_ok(&mut svm, ix_close_account(prog_id, adl_ins, lp.pubkey(), keeper.pubkey()), &payer, &[&payer, &lp]);
    send_ok(&mut svm, ix_close_account(prog_id, adl_mkt, lp.pubkey(), keeper.pubkey()), &payer, &[&payer, &lp]);
    let keeper_lam_1 = svm.get_account(&keeper.pubkey()).unwrap().lamports;
    assert_eq!(keeper_lam_1 - keeper_lam_0, 30_000_000, "All 3 closed accounts must return 100% rent!");

    let all_mkts2 = vec![btc_mkt, eth_mkt, scam_mkt];
    let all_pfls2 = vec![alice_pfl, bob_pfl, attacker_pfl, t2_pfl];
    assert_dex_invariants(&svm, &dex, &dex_vault, &all_mkts2, &all_pfls2, "post-suite6-close");
    println!("[PASS] Suite 6: Post-ADL ClearDeadLeg ({} CU) + WindDown/Tombstone + CloseAccount Rent Reclaim ({} CU)!", cu_clear, cu_close);

    // =========================================================================
    // SUITE 7 (NEW COMPOSABILITY): Bounded execPrice Spread, Authority Rotation,
    //          minMm Dust Floor, and Permissionless Insurance Donation!
    // =========================================================================
    let comp_mkt = create_prog_acc(&mut svm, &prog_id, MKT_SIZE);
    let comp_orc1 = Keypair::new();
    let comp_orc2 = Keypair::new();
    let comp_adm2 = Keypair::new();
    for kp in [&comp_orc1, &comp_orc2, &comp_adm2] {
        svm.airdrop(&kp.pubkey(), 10_000_000_000).unwrap();
    }
    // Create market with minMm = $5.00 (5_000_000) to prevent dust positions!
    send_ok(
        &mut svm,
        ix_create_market_ext(prog_id, dex, comp_mkt, mint, comp_orc1.pubkey(), lp.pubkey(), lp_tok, fee_vault,
            100 * POS_SCALE, 10, 50, 0, 1000, 500, 100, 0, 400, 2500, 1_000_000 * POS_SCALE, 5 * POS_SCALE),
        &payer,
        &[&payer, &lp],
    );
    // 7a. Permissionless insurance donation (donate=true, 0 LP shares minted!)
    send_ok(&mut svm, ix_deposit_insurance_ext(prog_id, dex, comp_mkt, comp_mkt, lp.pubkey(), lp_tok, mint, dex_vault, TOKEN_PROGRAM_ID, 25 * POS_SCALE, true), &payer, &[&payer, &lp]);
    assert_eq!(read_u64(&svm, &comp_mkt, 224), 25 * POS_SCALE); // insurance == $25
    assert_eq!(read_u64(&svm, &comp_mkt, 248), 0);              // totalInsShares == 0!

    // 7b. Authority rotation: rotate oracleAuth (comp_orc1 -> comp_orc2) & transfer marketAdmin (lp -> comp_adm2)!
    send_ok(&mut svm, ix_update_market_auth(prog_id, comp_mkt, lp.pubkey(), 1, comp_orc2.pubkey()), &payer, &[&payer, &lp]);
    set_slot(&mut svm, 161);
    send_err(&mut svm, ix_update_oracle(prog_id, comp_mkt, comp_orc1.pubkey(), 101 * POS_SCALE, 0, 0), &payer, &[&payer, &comp_orc1], "Old oracle rejected after rotation");
    send_ok(&mut svm, ix_update_oracle(prog_id, comp_mkt, comp_orc2.pubkey(), 101 * POS_SCALE, 0, 0), &payer, &[&payer, &comp_orc2]);
    send_ok(&mut svm, ix_update_market_auth(prog_id, comp_mkt, lp.pubkey(), 0, comp_adm2.pubkey()), &payer, &[&payer, &lp]);
    send_err(&mut svm, ix_burn_market_admin(prog_id, comp_mkt, lp.pubkey()), &payer, &[&payer, &lp], "Old marketAdmin rejected after transfer");
    send_ok(&mut svm, ix_burn_market_admin(prog_id, comp_mkt, comp_adm2.pubkey()), &payer, &[&payer, &comp_adm2]);

    // 7c. minMm dust floor ($5.00): tiny 0.01-unit trade ($1.01 notional) needs $5.00 margin;
    //     dust portfolio with $2.00 capital is REJECTED!
    let dust_kp = Keypair::new();
    svm.airdrop(&dust_kp.pubkey(), 10_000_000_000).unwrap();
    let dust_tok = create_tok_acc(&mut svm, &mint, &dust_kp.pubkey(), 100 * POS_SCALE);
    let dust_pfl = create_prog_acc(&mut svm, &prog_id, PFL_SIZE);
    send_ok(&mut svm, ix_init_portfolio(prog_id, dex, dust_pfl, dust_kp.pubkey()), &payer, &[&payer, &dust_kp]);
    send_ok(&mut svm, ix_deposit_collateral(prog_id, dex, dust_pfl, dust_kp.pubkey(), dust_tok, mint, dex_vault, TOKEN_PROGRAM_ID, 2 * POS_SCALE), &payer, &[&payer, &dust_kp]);
    send_err(&mut svm, ix_trade(prog_id, dex, comp_mkt, dust_pfl, dust_kp.pubkey(), t2_pfl, t2.pubkey(), 0, 10_000), &payer, &[&payer, &dust_kp, &t2], "Dust position rejected by minMm=$5 floor");

    // 7d. Bounded execPrice spread (external CLOB/AMM/matcher fill at $102 vs $101 mark = +$1.00 spread!):
    send_ok(&mut svm, ix_deposit_collateral(prog_id, dex, dust_pfl, dust_kp.pubkey(), dust_tok, mint, dex_vault, TOKEN_PROGRAM_ID, 20 * POS_SCALE), &payer, &[&payer, &dust_kp]);
    // Out-of-band execPrice ($120 vs $101 > 4% maxMove) REJECTED!
    send_err(&mut svm, ix_trade_ext(prog_id, dex, comp_mkt, dust_pfl, dust_kp.pubkey(), t2_pfl, t2.pubkey(), 0, POS_SCALE, 120 * POS_SCALE), &payer, &[&payer, &dust_kp, &t2], "Out-of-band execPrice rejected");
    let dust_cap_0 = read_u64(&svm, &dust_pfl, 88);
    let t2_cap_0 = read_u64(&svm, &t2_pfl, 88);
    // In-band execPrice ($102 vs $101 mark, qty=1.0 -> Long pays $1.00 spread directly to Short!)
    send_ok_assert_log(&mut svm, ix_trade_ext(prog_id, dex, comp_mkt, dust_pfl, dust_kp.pubkey(), t2_pfl, t2.pubkey(), 0, POS_SCALE, 102 * POS_SCALE), &payer, &[&payer, &dust_kp, &t2], "Program log: 0x2,");
    assert_eq!(read_u64(&svm, &dust_pfl, 88), dust_cap_0 - POS_SCALE, "Long must pay exact $1 spread to Short");
    assert_eq!(read_u64(&svm, &t2_pfl, 88), t2_cap_0 + POS_SCALE, "Short (LP/matcher) must receive exact $1 spread");

    // 7e. Donated-only market clean lifecycle: close OI -> stale WindDown -> ResolveMarket sweeps orphan $25
    //     donated insurance (totalInsShares == 0) into dex.totalSurplus -> TombstoneMarket succeeds!
    send_ok_assert_log(&mut svm, ix_trade(prog_id, dex, comp_mkt, dust_pfl, dust_kp.pubkey(), t2_pfl, t2.pubkey(), 1, POS_SCALE), &payer, &[&payer, &dust_kp, &t2], "Program log: 0x2,");
    let surp_before_donate_sweep = read_u64(&svm, &dex, 192);
    set_slot(&mut svm, 215); // > comp_mkt lastOracleSlot(161) + maxStaleness(50)
    send_ok(&mut svm, ix_start_wind_down(prog_id, comp_mkt, keeper.pubkey()), &payer, &[&payer, &keeper]);
    send_ok_assert_log(&mut svm, ix_resolve_market(prog_id, dex, comp_mkt), &payer, &[&payer], "Program log: 0x7,");
    assert_eq!(read_u64(&svm, &comp_mkt, 224), 0, "Orphan donated insurance must sweep to 0 on Resolve!");
    assert_eq!(read_u64(&svm, &dex, 192), surp_before_donate_sweep + 25 * POS_SCALE, "Orphan donated insurance must credit dex.totalSurplus!");
    send_ok(&mut svm, ix_tombstone_market(prog_id, comp_mkt), &payer, &[&payer]);
    assert_eq!(read_u8(&svm, &comp_mkt, 4), 3, "Donated-only market must reach STATUS_TOMBSTONED!");

    let all_mkts3 = vec![btc_mkt, eth_mkt, scam_mkt, comp_mkt];
    let all_pfls3 = vec![alice_pfl, bob_pfl, attacker_pfl, t2_pfl, dust_pfl];
    assert_dex_invariants(&svm, &dex, &dex_vault, &all_mkts3, &all_pfls3, "post-suite7-composability");
    println!("[PASS] Suite 7: External Matcher execPrice Spread + Authority Rotation + minMm Floor + Donated-Insurance Tombstone + Event Logs!");

    // =========================================================================
    // SUITE 8: 1,000-STEP RANDOMIZED STATEFUL FUZZER!
    //   Fresh DEX with 3 active markets + 5 cross-margin portfolios + 1 LP.
    //   Checks EXACT `C_tot + I_tot + R_tot + S_tot == V == SPL_balance`,
    //   exact `Σ pfl.capital == C_tot`, `Σ m.insurance == I_tot`, `Σ m.realizedPool == R_tot`,
    //   `oiLong == oiShort <= rawBasis`, `adl <= ADL_ONE`, `totalMm/totalIm` coherence
    //   after EVERY SINGLE TRANSACTION!
    // =========================================================================
    let f_dex = create_prog_acc(&mut svm, &prog_id, DEX_SIZE);
    let (f_vault, f_bump) = derive_dex_vault(&prog_id, &f_dex);
    send_ok(&mut svm, ix_init_dex(prog_id, f_dex, dex_admin.pubkey(), mint, f_vault, fee_vault, TOKEN_PROGRAM_ID, SYSTEM_PROGRAM_ID, f_bump, 6, 0, SPL_TOKEN_RENT_MIN), &payer, &[&payer, &dex_admin]);

    set_slot(&mut svm, 200);
    let mut f_oracles = Vec::new();
    let mut f_mkts = Vec::new();
    let mut f_mkt_pairs = Vec::new();
    let mut f_ins_accs = Vec::new();
    let mut f_prices = [100 * POS_SCALE, 50 * POS_SCALE, 200 * POS_SCALE];
    for m_i in 0..3usize {
        let orc = Keypair::new();
        svm.airdrop(&orc.pubkey(), 10_000_000_000).unwrap();
        let mkt = create_prog_acc(&mut svm, &prog_id, MKT_SIZE);
        let ins = create_prog_acc(&mut svm, &prog_id, INS_SIZE);
        send_ok(
            &mut svm,
            ix_create_market(prog_id, f_dex, mkt, mint, orc.pubkey(), dex_admin.pubkey(), alice_tok, fee_vault,
                f_prices[m_i], 10, 500, 0, 1000, 500, 100, 5, 400, 2500, 10_000 * POS_SCALE),
            &payer,
            &[&payer, &dex_admin],
        );
        send_ok(&mut svm, ix_deposit_insurance(prog_id, f_dex, mkt, ins, lp.pubkey(), lp_tok, mint, f_vault, TOKEN_PROGRAM_ID, 200 * POS_SCALE), &payer, &[&payer, &lp]);
        f_mkt_pairs.push(((m_i + 1) as u64, mkt));
        f_oracles.push(orc);
        f_mkts.push(mkt);
        f_ins_accs.push(ins);
    }

    let mut f_traders = Vec::new();
    let mut f_toks = Vec::new();
    let mut f_pfls = Vec::new();
    for _ in 0..5 {
        let kp = Keypair::new();
        svm.airdrop(&kp.pubkey(), 10_000_000_000).unwrap();
        let tok = create_tok_acc(&mut svm, &mint, &kp.pubkey(), 10_000 * POS_SCALE);
        let pfl = create_prog_acc(&mut svm, &prog_id, PFL_SIZE);
        send_ok(&mut svm, ix_init_portfolio(prog_id, f_dex, pfl, kp.pubkey()), &payer, &[&payer, &kp]);
        send_ok(&mut svm, ix_deposit_collateral(prog_id, f_dex, pfl, kp.pubkey(), tok, mint, f_vault, TOKEN_PROGRAM_ID, 80 * POS_SCALE), &payer, &[&payer, &kp]);
        f_traders.push(kp);
        f_toks.push(tok);
        f_pfls.push(pfl);
    }
    assert_dex_invariants(&svm, &f_dex, &f_vault, &f_mkts, &f_pfls, "fuzz-init");

    let mut rng = Rng(0x5EED_CAFE_2026_0001);
    let mut stats = [0u64; 8]; // [oracle, dep, wdr, open, reduce, refresh, liq, clearDead]
    let mut ok_txs = 0u64;
    let mut max_cu = 0u64;
    let mut trend_dir = [1i64, -1i64, 1i64];

    for step in 0..1000u64 {
        if step % 25 == 0 {
            for mi in 0..3 {
                trend_dir[mi] = if rng.range(2) == 0 { 1 } else { -1 };
            }
        }
        let act = rng.range(100);
        if act < 22 {
            // Advance slot + trend-biased clamped oracle move (exercises liquidations + ADL!)
            let cur = get_slot(&svm) + 1;
            set_slot(&mut svm, cur);
            let mi = rng.range(3) as usize;
            let mag = (rng.range(350) + 40) as i64; // 0.4% .. 3.9%
            let dir = if rng.range(4) == 0 { -trend_dir[mi] } else { trend_dir[mi] };
            let bps_delta = (dir * mag).clamp(-380, 380);
            let cur_p = read_u64(&svm, &f_mkts[mi], 112);
            let mut new_p = ((cur_p as i128) * (10_000 + bps_delta as i128) / 10_000) as u64;
            new_p = new_p.clamp(5 * POS_SCALE, 500 * POS_SCALE);
            let fund_sign = rng.range(2) as u8;
            let fund_e6 = rng.range(cur_p / 2000 + 1);
            if let Ok(cu) = send_ixs_try(&mut svm, &[ix_update_oracle(prog_id, f_mkts[mi], f_oracles[mi].pubkey(), new_p, fund_sign, fund_e6)], &payer, &[&payer, &f_oracles[mi]]) {
                f_prices[mi] = new_p;
                stats[0] += 1;
                ok_txs += 1;
                max_cu = max_cu.max(cu);
            }
        } else if act < 28 {
            // DepositCollateral
            let ti = rng.range(5) as usize;
            let amt = (rng.range(30) + 10) * POS_SCALE;
            if let Ok(cu) = send_ixs_try(&mut svm, &[ix_deposit_collateral(prog_id, f_dex, f_pfls[ti], f_traders[ti].pubkey(), f_toks[ti], mint, f_vault, TOKEN_PROGRAM_ID, amt)], &payer, &[&payer, &f_traders[ti]]) {
                stats[1] += 1;
                ok_txs += 1;
                max_cu = max_cu.max(cu);
            }
        } else if act < 35 {
            // Atomic [RefreshLeg..., WithdrawCollateral]
            let ti = rng.range(5) as usize;
            let amt = (rng.range(20) + 1) * POS_SCALE;
            let mut ixs = refresh_open_legs_ixs(&svm, prog_id, f_dex, f_pfls[ti], &f_mkt_pairs);
            ixs.push(ix_withdraw_collateral(prog_id, f_dex, f_pfls[ti], f_traders[ti].pubkey(), f_toks[ti], mint, f_vault, TOKEN_PROGRAM_ID, amt));
            if let Ok(cu) = send_ixs_try(&mut svm, &ixs, &payer, &[&payer, &f_traders[ti]]) {
                stats[2] += 1;
                ok_txs += 1;
                max_cu = max_cu.max(cu);
            }
        } else if act < 60 {
            // Trade Open (higher leverage: 2..6 units, with atomic pre-refresh!)
            let mi = rng.range(3) as usize;
            let tl = rng.range(5) as usize;
            let mut ts = rng.range(5) as usize;
            if ts == tl { ts = (ts + 1) % 5; }
            let qty = (rng.range(5) + 2) * POS_SCALE;
            let mut ixs = refresh_open_legs_ixs(&svm, prog_id, f_dex, f_pfls[tl], &f_mkt_pairs);
            ixs.extend(refresh_open_legs_ixs(&svm, prog_id, f_dex, f_pfls[ts], &f_mkt_pairs));
            ixs.push(ix_trade(prog_id, f_dex, f_mkts[mi], f_pfls[tl], f_traders[tl].pubkey(), f_pfls[ts], f_traders[ts].pubkey(), 0, qty));
            if let Ok(cu) = send_ixs_try(&mut svm, &ixs, &payer, &[&payer, &f_traders[tl], &f_traders[ts]]) {
                stats[3] += 1;
                ok_txs += 1;
                max_cu = max_cu.max(cu);
            }
        } else if act < 72 {
            // Trade Reduce
            let mi = rng.range(3) as usize;
            let tl = rng.range(5) as usize;
            let mut ts = rng.range(5) as usize;
            if ts == tl { ts = (ts + 1) % 5; }
            let qty = (rng.range(3) + 1) * POS_SCALE;
            if let Ok(cu) = send_ixs_try(&mut svm, &[ix_trade(prog_id, f_dex, f_mkts[mi], f_pfls[tl], f_traders[tl].pubkey(), f_pfls[ts], f_traders[ts].pubkey(), 1, qty)], &payer, &[&payer, &f_traders[tl], &f_traders[ts]]) {
                stats[4] += 1;
                ok_txs += 1;
                max_cu = max_cu.max(cu);
            }
        } else if act < 82 {
            // RefreshLeg
            let mi = rng.range(3) as usize;
            let ti = rng.range(5) as usize;
            let force = rng.range(4) == 0;
            if let Ok(cu) = send_ixs_try(&mut svm, &[ix_refresh_leg(prog_id, f_dex, f_mkts[mi], f_pfls[ti], force)], &payer, &[&payer]) {
                stats[5] += 1;
                ok_txs += 1;
                max_cu = max_cu.max(cu);
            }
        } else if act < 93 {
            // Liquidate sweep across all markets & traders: refresh all OTHER open legs (A1),
            // leaving target market `f_mkts[mi]` for `Liquidate` itself so `shortfall > 0` triggers `I_m` draw!
            let mi = rng.range(3) as usize;
            let ti = rng.range(5) as usize;
            let other_pairs: Vec<(u64, Address)> = f_mkt_pairs.iter().copied().filter(|&(_, m)| m != f_mkts[mi]).collect();
            let mut ixs = refresh_open_legs_ixs(&svm, prog_id, f_dex, f_pfls[ti], &other_pairs);
            ixs.push(ix_liquidate(prog_id, f_dex, f_mkts[mi], f_pfls[ti], keeper_tok, mint, f_vault, TOKEN_PROGRAM_ID));
            if let Ok(cu) = send_ixs_try(&mut svm, &ixs, &payer, &[&payer]) {
                stats[6] += 1;
                ok_txs += 1;
                max_cu = max_cu.max(cu);
            }
        } else {
            // ClearDeadLeg sweep
            let mi = rng.range(3) as usize;
            let ti = rng.range(5) as usize;
            if let Ok(cu) = send_ixs_try(&mut svm, &[ix_clear_dead_leg(prog_id, f_dex, f_mkts[mi], f_pfls[ti])], &payer, &[&payer]) {
                stats[7] += 1;
                ok_txs += 1;
                max_cu = max_cu.max(cu);
            }
        }

        // Assert EVERY SINGLE GLOBAL & LOCAL INVARIANT AFTER EVERY STEP!
        assert_dex_invariants(&svm, &f_dex, &f_vault, &f_mkts, &f_pfls, &format!("fuzz-step-{}", step));
    }

    println!(
        "[PASS] Suite 8: 1,000-Step Stateful Fuzzer — {} valid txs, ZERO invariant violations! (oracle={}, dep={}, wdr={}, open={}, red={}, ref={}, liq={}, clearDead={}, max_cu={})",
        ok_txs, stats[0], stats[1], stats[2], stats[3], stats[4], stats[5], stats[6], stats[7], max_cu
    );

    // =========================================================================
    // SUITE 9: EXTERNAL PROGRAM COMPOSITION (CPI) —
    //   9A: `oracle_adapter.so` (Permissionless external price feed + auto-clamp + funding!)
    //   9B: `matcher.so` (Passive LP AMM / Spread Matcher — single-signer Taker open & close!)
    // =========================================================================
    let matcher_path = std::env::args().nth(2).unwrap_or_else(|| "build/matcher.so".to_string());
    let adapter_path = std::env::args().nth(3).unwrap_or_else(|| "build/oracle_adapter.so".to_string());
    let matcher_elf = std::fs::read(&matcher_path).unwrap_or_else(|e| panic!("Failed to read {}: {}", matcher_path, e));
    let adapter_elf = std::fs::read(&adapter_path).unwrap_or_else(|e| panic!("Failed to read {}: {}", adapter_path, e));
    let matcher_prog = Keypair::new().pubkey();
    let adapter_prog = Keypair::new().pubkey();
    svm.add_program(matcher_prog, &matcher_elf).expect("matcher ELF load failed");
    svm.add_program(adapter_prog, &adapter_elf).expect("adapter ELF load failed");

    // 9A: OracleAdapter CPI composition (Custom + Pyth V2 + Chainlink OCR2 + Switchboard + 2-Leg Ratio!)
    let comp_mkt2 = create_prog_acc(&mut svm, &prog_id, MKT_SIZE);
    let adp_acc = create_prog_acc(&mut svm, &adapter_prog, 352);
    let (orac_pda, orac_bump) = Address::find_program_address(&[b"orac", adp_acc.as_ref()], &adapter_prog);
    // External on-chain price feed account (32B: magic="FEED", price, conf, publishSlot)
    let feed_acc = Keypair::new().pubkey();
    let write_feed = |svm: &mut LiteSVM, price: u64, conf: u64, pub_slot: u64| {
        let mut d = vec![0u8; 32];
        d[0..4].copy_from_slice(&0x44454546u32.to_le_bytes()); // "FEED"
        d[8..16].copy_from_slice(&price.to_le_bytes());
        d[16..24].copy_from_slice(&conf.to_le_bytes());
        d[24..32].copy_from_slice(&pub_slot.to_le_bytes());
        svm.set_account(feed_acc, Account { lamports: 10_000_000, data: d, owner: SYSTEM_PROGRAM_ID, executable: false, rent_epoch: 0 }).unwrap();
    };
    let s0 = get_slot(&svm) + 1;
    set_slot(&mut svm, s0);
    write_feed(&mut svm, 115 * POS_SCALE, 50_000, s0); // $115.00, conf $0.05

    // Create market with `orac_pda` (owned by OracleAdapter!) as oracleAuth!
    send_ok(
        &mut svm,
        ix_create_market(prog_id, dex, comp_mkt2, mint, orac_pda, lp.pubkey(), lp_tok, fee_vault,
            100 * POS_SCALE, 10, 50, 0, 1000, 500, 100, 0, 400, 2500, 1_000_000 * POS_SCALE),
        &payer,
        &[&payer, &lp],
    );
    // InitAdapter (maxFeedAge=10, maxConfBps=100=1%, fundingBpsPerStep=10)
    let mut init_adp_data = vec![0u8; 28];
    init_adp_data[0] = 0;
    init_adp_data[1] = orac_bump;
    init_adp_data[4..12].copy_from_slice(&10u64.to_le_bytes());
    init_adp_data[12..20].copy_from_slice(&100u64.to_le_bytes());
    init_adp_data[20..28].copy_from_slice(&10u64.to_le_bytes());
    send_ok(
        &mut svm,
        Instruction {
            program_id: adapter_prog,
            accounts: vec![
                AccountMeta::new(adp_acc, false),
                AccountMeta::new_readonly(lp.pubkey(), true),
                AccountMeta::new_readonly(prog_id, false),
                AccountMeta::new_readonly(comp_mkt2, false),
                AccountMeta::new_readonly(feed_acc, false),
            ],
            data: init_adp_data,
        },
        &payer,
        &[&payer, &lp],
    );
    let ix_crank = || Instruction {
        program_id: adapter_prog,
        accounts: vec![
            AccountMeta::new_readonly(adp_acc, false),
            AccountMeta::new(comp_mkt2, false),
            AccountMeta::new_readonly(feed_acc, false),
            AccountMeta::new_readonly(orac_pda, false),
            AccountMeta::new_readonly(prog_id, false),
        ],
        data: vec![1],
    };
    // Reject stale feed, wide confidence, AND spoofed feed account owner!
    set_slot(&mut svm, s0 + 20);
    send_err(&mut svm, ix_crank(), &payer, &[&payer], "OracleAdapter rejects stale feed");
    write_feed(&mut svm, 115 * POS_SCALE, 5 * POS_SCALE, s0 + 20); // conf $5 > 1%
    send_err(&mut svm, ix_crank(), &payer, &[&payer], "OracleAdapter rejects wide confidence");
    {
        let mut spoofed = svm.get_account(&feed_acc).unwrap();
        spoofed.owner = Keypair::new().pubkey();
        let mut d = vec![0u8; 32];
        d[0..4].copy_from_slice(&0x44454546u32.to_le_bytes());
        d[8..16].copy_from_slice(&(115 * POS_SCALE).to_le_bytes());
        d[16..24].copy_from_slice(&50_000u64.to_le_bytes());
        d[24..32].copy_from_slice(&(s0 + 20).to_le_bytes());
        spoofed.data = d;
        svm.set_account(feed_acc, spoofed).unwrap();
        send_err(&mut svm, ix_crank(), &payer, &[&payer], "OracleAdapter rejects spoofed feed owner");
    }

    // Permissionless 4-slot smooth auto-clamped convergence ($100 -> $104 -> $108.16 -> $112.4864 -> $115.00)!
    let mut cu_crank = 0u64;
    for step in 1..=4u64 {
        let sl = s0 + 20 + step;
        set_slot(&mut svm, sl);
        write_feed(&mut svm, 115 * POS_SCALE, 50_000, sl);
        cu_crank = send_ok_assert_log(&mut svm, ix_crank(), &payer, &[&payer], "Program log: 0x1,");
    }
    assert_eq!(read_u64(&svm, &comp_mkt2, 112), 115 * POS_SCALE, "OracleAdapter converged smoothly to $115!");

    // 9A-2: Native Pyth V2 (`PriceUpdateV2`), Chainlink OCR2 (`Transmissions`),
    //       Switchboard On-Demand (`PullFeedAccountData`), AND 2-Leg Composite Ratio (`Pyth / Chainlink`)!
    let mut clock_now: Clock = svm.get_sysvar();
    clock_now.slot = s0 + 30;
    clock_now.unix_timestamp = 1_750_000_000;
    svm.set_sysvar(&clock_now);
    svm.expire_blockhash();

    let pyth_prog_id = Address::from_str_const("rec5EKMGg6MxZYaMdyBfgwp4d5rB9T1VQH5pJv5LtFJ");
    let cl_prog_id   = Address::from_str_const("HEvSKofvBgfaexv23kMabbYqxasxU3mQ4ibBMEmJWHny");
    let sb_prog_id   = Address::from_str_const("SBondMDrcV3K4kxZR1HNVT7osZxAHVHgYXL5Ze1oMUv");

    let make_pyth_v2 = |feed_id: [u8; 32], price: i64, conf: u64, expo: i32, pub_ts: i64, posted_slot: u64, ver: u8| -> Vec<u8> {
        let mut d = vec![0u8; 133];
        d[0..8].copy_from_slice(&[34, 241, 35, 99, 157, 126, 244, 205]);
        d[40] = ver;
        d[41..73].copy_from_slice(&feed_id);
        d[73..81].copy_from_slice(&price.to_le_bytes());
        d[81..89].copy_from_slice(&conf.to_le_bytes());
        d[89..93].copy_from_slice(&expo.to_le_bytes());
        d[93..101].copy_from_slice(&pub_ts.to_le_bytes());
        d[125..133].copy_from_slice(&posted_slot.to_le_bytes());
        d
    };
    let make_chainlink_ocr2 = |decimals: u8, live_len: u32, live_cur: u32, slot: u64, answer: i128| -> Vec<u8> {
        let mut d = vec![0u8; 200 + (live_len as usize) * 48];
        d[0..8].copy_from_slice(&[96, 179, 69, 66, 128, 129, 73, 117]);
        d[8] = 2;
        d[138] = decimals;
        d[143..147].copy_from_slice(&7u32.to_le_bytes());
        d[148..152].copy_from_slice(&live_len.to_le_bytes());
        d[152..156].copy_from_slice(&live_cur.to_le_bytes());
        let idx = ((live_cur + live_len - 1) % live_len) as usize;
        let off = 200 + idx * 48;
        d[off..off + 8].copy_from_slice(&slot.to_le_bytes());
        d[off + 16..off + 32].copy_from_slice(&answer.to_le_bytes());
        d
    };
    let make_switchboard = |value: i128, std_dev: i128, num_samples: u8, slot: u64| -> Vec<u8> {
        let mut d = vec![0u8; 3208];
        d[0..8].copy_from_slice(&[196, 27, 108, 196, 10, 215, 219, 40]);
        d[2264..2280].copy_from_slice(&value.to_le_bytes());
        d[2280..2296].copy_from_slice(&std_dev.to_le_bytes());
        d[2360] = num_samples;
        d[2368..2376].copy_from_slice(&slot.to_le_bytes());
        d
    };

    // (a) Pyth V2 Parser Test ($100 -> $103.00 at expo = -8, pinned feed_id & owner)
    let pyth_fid = [0xABu8; 32];
    let pyth_feed = Keypair::new().pubkey();
    let pyth_mkt = create_prog_acc(&mut svm, &prog_id, MKT_SIZE);
    let pyth_adp = create_prog_acc(&mut svm, &adapter_prog, 352);
    let (pyth_pda, pyth_bump) = Address::find_program_address(&[b"orac", pyth_adp.as_ref()], &adapter_prog);
    svm.set_account(pyth_feed, Account { lamports: 10_000_000, data: make_pyth_v2(pyth_fid, 10_300_000_000, 5_000_000, -8, 1_750_000_000, s0 + 30, 1), owner: pyth_prog_id, executable: false, rent_epoch: 0 }).unwrap();
    send_ok(&mut svm, ix_create_market(prog_id, dex, pyth_mkt, mint, pyth_pda, lp.pubkey(), lp_tok, fee_vault, 100 * POS_SCALE, 10, 50, 0, 1000, 500, 100, 0, 400, 2500, 1_000_000 * POS_SCALE), &payer, &[&payer, &lp]);
    let mut pyth_init = vec![0u8; 60];
    pyth_init[0] = 0; pyth_init[1] = pyth_bump; pyth_init[2] = 1;
    pyth_init[4..12].copy_from_slice(&30u64.to_le_bytes());
    pyth_init[12..20].copy_from_slice(&100u64.to_le_bytes());
    pyth_init[28..60].copy_from_slice(&pyth_fid);
    send_ok(&mut svm, Instruction { program_id: adapter_prog, accounts: vec![
        AccountMeta::new(pyth_adp, false), AccountMeta::new_readonly(lp.pubkey(), true),
        AccountMeta::new_readonly(prog_id, false), AccountMeta::new_readonly(pyth_mkt, false),
        AccountMeta::new_readonly(pyth_feed, false),
    ], data: pyth_init }, &payer, &[&payer, &lp]);
    let ix_pyth_crank = || Instruction { program_id: adapter_prog, accounts: vec![
        AccountMeta::new_readonly(pyth_adp, false), AccountMeta::new(pyth_mkt, false),
        AccountMeta::new_readonly(pyth_feed, false), AccountMeta::new_readonly(pyth_pda, false),
        AccountMeta::new_readonly(prog_id, false),
    ], data: vec![1] };
    let mut c1: Clock = svm.get_sysvar(); c1.slot = s0 + 31; c1.unix_timestamp = 1_750_000_005; svm.set_sysvar(&c1);
    svm.set_account(pyth_feed, Account { lamports: 10_000_000, data: make_pyth_v2(pyth_fid, 10_300_000_000, 5_000_000, -8, 1_750_000_000, s0 + 31, 0), owner: pyth_prog_id, executable: false, rent_epoch: 0 }).unwrap();
    send_err_custom(&mut svm, ix_pyth_crank(), &payer, &[&payer], 304, "Pyth rejects VerificationLevel::Partial");
    svm.set_account(pyth_feed, Account { lamports: 10_000_000, data: make_pyth_v2([0xCDu8; 32], 10_300_000_000, 5_000_000, -8, 1_750_000_000, s0 + 31, 1), owner: pyth_prog_id, executable: false, rent_epoch: 0 }).unwrap();
    send_err_custom(&mut svm, ix_pyth_crank(), &payer, &[&payer], 305, "Pyth rejects mismatched feed_id");
    svm.set_account(pyth_feed, Account { lamports: 10_000_000, data: make_pyth_v2(pyth_fid, 10_300_000_000, 5_000_000, -8, 1_749_999_900, s0 + 31, 1), owner: pyth_prog_id, executable: false, rent_epoch: 0 }).unwrap();
    send_err_custom(&mut svm, ix_pyth_crank(), &payer, &[&payer], 300, "Pyth rejects stale publish_time");
    svm.set_account(pyth_feed, Account { lamports: 10_000_000, data: make_pyth_v2(pyth_fid, 10_300_000_000, 5_000_000, -8, 1_750_000_004, s0 + 31, 1), owner: pyth_prog_id, executable: false, rent_epoch: 0 }).unwrap();
    let cu_pyth = send_ok_assert_log(&mut svm, ix_pyth_crank(), &payer, &[&payer], "Program log: 0x1,");
    assert_eq!(read_u64(&svm, &pyth_mkt, 112), 103 * POS_SCALE, "Pyth V2 parsed $103.00 (expo -8 -> E6)!");

    // (b) Chainlink OCR2 Parser Test ($100 -> $102.50, ring-buffer wraparound live_cursor=0, live_len=4, decimals=8)
    let cl_feed = Keypair::new().pubkey();
    let cl_mkt = create_prog_acc(&mut svm, &prog_id, MKT_SIZE);
    let cl_adp = create_prog_acc(&mut svm, &adapter_prog, 352);
    let (cl_pda, cl_bump) = Address::find_program_address(&[b"orac", cl_adp.as_ref()], &adapter_prog);
    svm.set_account(cl_feed, Account { lamports: 10_000_000, data: make_chainlink_ocr2(8, 4, 0, s0 + 31, 10_250_000_000i128), owner: cl_prog_id, executable: false, rent_epoch: 0 }).unwrap();
    send_ok(&mut svm, ix_create_market(prog_id, dex, cl_mkt, mint, cl_pda, lp.pubkey(), lp_tok, fee_vault, 100 * POS_SCALE, 10, 50, 0, 1000, 500, 100, 0, 400, 2500, 1_000_000 * POS_SCALE), &payer, &[&payer, &lp]);
    let mut cl_init = vec![0u8; 28];
    cl_init[0] = 0; cl_init[1] = cl_bump; cl_init[2] = 2;
    cl_init[4..12].copy_from_slice(&10u64.to_le_bytes());
    cl_init[12..20].copy_from_slice(&100u64.to_le_bytes());
    send_ok(&mut svm, Instruction { program_id: adapter_prog, accounts: vec![
        AccountMeta::new(cl_adp, false), AccountMeta::new_readonly(lp.pubkey(), true),
        AccountMeta::new_readonly(prog_id, false), AccountMeta::new_readonly(cl_mkt, false),
        AccountMeta::new_readonly(cl_feed, false),
    ], data: cl_init }, &payer, &[&payer, &lp]);
    let mut c2: Clock = svm.get_sysvar(); c2.slot = s0 + 32; c2.unix_timestamp = 1_750_000_006; svm.set_sysvar(&c2);
    let cu_cl = send_ok_assert_log(&mut svm, Instruction { program_id: adapter_prog, accounts: vec![
        AccountMeta::new_readonly(cl_adp, false), AccountMeta::new(cl_mkt, false),
        AccountMeta::new_readonly(cl_feed, false), AccountMeta::new_readonly(cl_pda, false),
        AccountMeta::new_readonly(prog_id, false),
    ], data: vec![1] }, &payer, &[&payer], "Program log: 0x1,");
    assert_eq!(read_u64(&svm, &cl_mkt, 112), 102_500_000, "Chainlink OCR2 parsed $102.50 with ring wraparound!");

    // (c) Switchboard On-Demand Parser Test ($100 -> $104.00, full 128-bit PRECISION=18 scaling!)
    let sb_feed = Keypair::new().pubkey();
    let sb_mkt = create_prog_acc(&mut svm, &prog_id, MKT_SIZE);
    let sb_adp = create_prog_acc(&mut svm, &adapter_prog, 352);
    let (sb_pda, sb_bump) = Address::find_program_address(&[b"orac", sb_adp.as_ref()], &adapter_prog);
    let sb_val: i128 = 104i128 * 1_000_000_000_000_000_000i128;
    let sb_std: i128 = 100_000_000_000_000_000i128;
    svm.set_account(sb_feed, Account { lamports: 10_000_000, data: make_switchboard(sb_val, sb_std, 5, s0 + 32), owner: sb_prog_id, executable: false, rent_epoch: 0 }).unwrap();
    send_ok(&mut svm, ix_create_market(prog_id, dex, sb_mkt, mint, sb_pda, lp.pubkey(), lp_tok, fee_vault, 100 * POS_SCALE, 10, 50, 0, 1000, 500, 100, 0, 400, 2500, 1_000_000 * POS_SCALE), &payer, &[&payer, &lp]);
    let mut sb_init = vec![0u8; 28];
    sb_init[0] = 0; sb_init[1] = sb_bump; sb_init[2] = 3;
    sb_init[4..12].copy_from_slice(&10u64.to_le_bytes());
    sb_init[12..20].copy_from_slice(&100u64.to_le_bytes());
    send_ok(&mut svm, Instruction { program_id: adapter_prog, accounts: vec![
        AccountMeta::new(sb_adp, false), AccountMeta::new_readonly(lp.pubkey(), true),
        AccountMeta::new_readonly(prog_id, false), AccountMeta::new_readonly(sb_mkt, false),
        AccountMeta::new_readonly(sb_feed, false),
    ], data: sb_init }, &payer, &[&payer, &lp]);
    let mut c3: Clock = svm.get_sysvar(); c3.slot = s0 + 33; c3.unix_timestamp = 1_750_000_007; svm.set_sysvar(&c3);
    let cu_sb = send_ok_assert_log(&mut svm, Instruction { program_id: adapter_prog, accounts: vec![
        AccountMeta::new_readonly(sb_adp, false), AccountMeta::new(sb_mkt, false),
        AccountMeta::new_readonly(sb_feed, false), AccountMeta::new_readonly(sb_pda, false),
        AccountMeta::new_readonly(prog_id, false),
    ], data: vec![1] }, &payer, &[&payer], "Program log: 0x1,");
    assert_eq!(read_u64(&svm, &sb_mkt, 112), 104 * POS_SCALE, "Switchboard On-Demand parsed $104.00 (128-bit E18 -> E6)!");

    // (d) 2-Leg Composite Ratio Market (`Pyth V2 $500` / `Chainlink OCR2 $125` = `4.00` — e.g. STOXX/SOL!)
    let rat_mkt = create_prog_acc(&mut svm, &prog_id, MKT_SIZE);
    let rat_adp = create_prog_acc(&mut svm, &adapter_prog, 352);
    let (rat_pda, rat_bump) = Address::find_program_address(&[b"orac", rat_adp.as_ref()], &adapter_prog);
    let stoxx_feed = Keypair::new().pubkey();
    let sol_feed   = Keypair::new().pubkey();
    let stoxx_fid  = [0x55u8; 32];
    svm.set_account(stoxx_feed, Account { lamports: 10_000_000, data: make_pyth_v2(stoxx_fid, 50_000_000_000, 10_000_000, -8, 1_750_000_007, s0 + 33, 1), owner: pyth_prog_id, executable: false, rent_epoch: 0 }).unwrap();
    svm.set_account(sol_feed,   Account { lamports: 10_000_000, data: make_chainlink_ocr2(8, 4, 2, s0 + 33, 12_500_000_000i128), owner: cl_prog_id, executable: false, rent_epoch: 0 }).unwrap();
    send_ok(&mut svm, ix_create_market(prog_id, dex, rat_mkt, mint, rat_pda, lp.pubkey(), lp_tok, fee_vault, 3_950_000, 10, 50, 0, 1000, 500, 100, 0, 400, 2500, 1_000_000 * POS_SCALE), &payer, &[&payer, &lp]);
    let mut rat_init = vec![0u8; 60];
    rat_init[0] = 0; rat_init[1] = rat_bump; rat_init[2] = 1; rat_init[3] = 2;
    rat_init[4..12].copy_from_slice(&30u64.to_le_bytes());
    rat_init[12..20].copy_from_slice(&100u64.to_le_bytes());
    rat_init[28..60].copy_from_slice(&stoxx_fid);
    send_ok(&mut svm, Instruction { program_id: adapter_prog, accounts: vec![
        AccountMeta::new(rat_adp, false), AccountMeta::new_readonly(lp.pubkey(), true),
        AccountMeta::new_readonly(prog_id, false), AccountMeta::new_readonly(rat_mkt, false),
        AccountMeta::new_readonly(stoxx_feed, false), AccountMeta::new_readonly(sol_feed, false),
    ], data: rat_init }, &payer, &[&payer, &lp]);
    let mut c4: Clock = svm.get_sysvar(); c4.slot = s0 + 34; c4.unix_timestamp = 1_750_000_008; svm.set_sysvar(&c4);
    let cu_ratio = send_ok_assert_log(&mut svm, Instruction { program_id: adapter_prog, accounts: vec![
        AccountMeta::new_readonly(rat_adp, false), AccountMeta::new(rat_mkt, false),
        AccountMeta::new_readonly(stoxx_feed, false), AccountMeta::new_readonly(rat_pda, false),
        AccountMeta::new_readonly(prog_id, false), AccountMeta::new_readonly(sol_feed, false),
    ], data: vec![1] }, &payer, &[&payer], "Program log: 0x1,");
    assert_eq!(read_u64(&svm, &rat_mkt, 112), 4 * POS_SCALE, "2-Leg Ratio Pyth($500)/Chainlink($125) converged to exact 4.00!");

    // (e) EWMA Smoothing + Hybrid After-Hours 2-Leg STOXX/SOL + Bounded PushEwmaMark!
    let ewma_mkt = create_prog_acc(&mut svm, &prog_id, MKT_SIZE);
    let ewma_adp = create_prog_acc(&mut svm, &adapter_prog, 352);
    let (ewma_pda, ewma_bump) = Address::find_program_address(&[b"orac", ewma_adp.as_ref()], &adapter_prog);
    send_ok(&mut svm, ix_create_market(prog_id, dex, ewma_mkt, mint, ewma_pda, lp.pubkey(), lp_tok, fee_vault, 4 * POS_SCALE, 10, 50, 0, 1000, 500, 100, 0, 400, 2500, 1_000_000 * POS_SCALE), &payer, &[&payer, &lp]);
    let mut ewma_init = vec![0u8; 60];
    ewma_init[0] = 0; ewma_init[1] = ewma_bump; ewma_init[2] = 1; ewma_init[3] = 2;
    ewma_init[4..12].copy_from_slice(&30u64.to_le_bytes());
    ewma_init[12..20].copy_from_slice(&100u64.to_le_bytes());
    ewma_init[28..60].copy_from_slice(&stoxx_fid);
    send_ok(&mut svm, Instruction { program_id: adapter_prog, accounts: vec![
        AccountMeta::new(ewma_adp, false), AccountMeta::new_readonly(lp.pubkey(), true),
        AccountMeta::new_readonly(prog_id, false), AccountMeta::new_readonly(ewma_mkt, false),
        AccountMeta::new_readonly(stoxx_feed, false), AccountMeta::new_readonly(sol_feed, false),
    ], data: ewma_init }, &payer, &[&payer, &lp]);
    // Op 2: One-shot InitEwma (hybridAH=1, alphaBps=2000 [20%], maxDevBps=500 [5%], initEwmaPrice=$500)
    let mut init_ewma_data = vec![0u8; 26];
    init_ewma_data[0] = 2;
    init_ewma_data[1] = 1;
    init_ewma_data[2..10].copy_from_slice(&2000u64.to_le_bytes());
    init_ewma_data[10..18].copy_from_slice(&500u64.to_le_bytes());
    init_ewma_data[18..26].copy_from_slice(&(500 * POS_SCALE).to_le_bytes());
    let ix_init_ewma = Instruction {
        program_id: adapter_prog,
        accounts: vec![AccountMeta::new(ewma_adp, false), AccountMeta::new_readonly(lp.pubkey(), true)],
        data: init_ewma_data,
    };
    send_ok(&mut svm, ix_init_ewma.clone(), &payer, &[&payer, &lp]);
    send_err(&mut svm, ix_init_ewma, &payer, &[&payer, &lp], "InitEwma must be strictly one-shot immutable");

    let ix_ewma_crank = || Instruction {
        program_id: adapter_prog,
        accounts: vec![
            AccountMeta::new(ewma_adp, false), AccountMeta::new(ewma_mkt, false),
            AccountMeta::new_readonly(stoxx_feed, false), AccountMeta::new_readonly(ewma_pda, false),
            AccountMeta::new_readonly(prog_id, false), AccountMeta::new_readonly(sol_feed, false),
        ],
        data: vec![1],
    };
    let ix_push_ewma = |signer: Address, mark_e6: u64| {
        let mut d = vec![0u8; 9];
        d[0] = 3;
        d[1..9].copy_from_slice(&mark_e6.to_le_bytes());
        Instruction {
            program_id: adapter_prog,
            accounts: vec![AccountMeta::new(ewma_adp, false), AccountMeta::new_readonly(signer, true)],
            data: d,
        }
    };

    // (e1) Live hours: STOXX jumps $500 -> $510 (fresh Pyth), SOL=$125 (fresh Chainlink)
    //      EWMA(20%) = 500*0.8 + 510*0.2 = $502.00; STOXX/SOL = 502/125 = 4.016000!
    let mut c5: Clock = svm.get_sysvar(); c5.slot = s0 + 35; c5.unix_timestamp = 1_750_000_010; svm.set_sysvar(&c5);
    svm.set_account(stoxx_feed, Account { lamports: 10_000_000, data: make_pyth_v2(stoxx_fid, 51_000_000_000, 10_000_000, -8, 1_750_000_009, s0 + 35, 1), owner: pyth_prog_id, executable: false, rent_epoch: 0 }).unwrap();
    svm.set_account(sol_feed,   Account { lamports: 10_000_000, data: make_chainlink_ocr2(8, 4, 2, s0 + 35, 12_500_000_000i128), owner: cl_prog_id, executable: false, rent_epoch: 0 }).unwrap();
    let cu_ewma_live = send_ok_assert_log(&mut svm, ix_ewma_crank(), &payer, &[&payer], "Program log: 0x1,");
    assert_eq!(read_u64(&svm, &ewma_adp, 328), 502 * POS_SCALE, "Live EWMA(20%) $500->$510 = $502.00!");
    assert_eq!(read_u64(&svm, &ewma_mkt, 112), 4_016_000, "Live EWMA STOXX/SOL = 502/125 = 4.016!");

    // (e2) After-hours: STOXX closes (stale by +3,600s > 30s!), SOL moves live $125 -> $128!
    //      Verify spoofed feed_id is STILL rejected, stale 24/7 quote SOL is STILL rejected,
    //      and valid after-hours Crank carries ewma(STOXX)=$502 / live(SOL)=$128 = 3.921875!
    let mut c6: Clock = svm.get_sysvar(); c6.slot = s0 + 36; c6.unix_timestamp = 1_750_003_610; svm.set_sysvar(&c6);
    svm.set_account(stoxx_feed, Account { lamports: 10_000_000, data: make_pyth_v2([0xEEu8; 32], 51_000_000_000, 10_000_000, -8, 1_750_000_009, s0 + 35, 1), owner: pyth_prog_id, executable: false, rent_epoch: 0 }).unwrap();
    svm.set_account(sol_feed,   Account { lamports: 10_000_000, data: make_chainlink_ocr2(8, 4, 2, s0 + 36, 12_800_000_000i128), owner: cl_prog_id, executable: false, rent_epoch: 0 }).unwrap();
    send_err_custom(&mut svm, ix_ewma_crank(), &payer, &[&payer], 305, "After-hours still rejects wrong Pyth feed_id");
    svm.set_account(stoxx_feed, Account { lamports: 10_000_000, data: make_pyth_v2(stoxx_fid, 51_000_000_000, 10_000_000, -8, 1_750_000_009, s0 + 35, 1), owner: pyth_prog_id, executable: false, rent_epoch: 0 }).unwrap();
    svm.set_account(sol_feed,   Account { lamports: 10_000_000, data: make_chainlink_ocr2(8, 4, 2, s0 + 1,  12_800_000_000i128), owner: cl_prog_id, executable: false, rent_epoch: 0 }).unwrap();
    send_err_custom(&mut svm, ix_ewma_crank(), &payer, &[&payer], 300, "After-hours still rejects stale 24/7 quote feed");
    svm.set_account(sol_feed,   Account { lamports: 10_000_000, data: make_chainlink_ocr2(8, 4, 2, s0 + 36, 12_800_000_000i128), owner: cl_prog_id, executable: false, rent_epoch: 0 }).unwrap();
    let cu_ewma_ah = send_ok_assert_log(&mut svm, ix_ewma_crank(), &payer, &[&payer], "Program log: 0x1,");
    assert_eq!(read_u64(&svm, &ewma_adp, 328), 502 * POS_SCALE, "After-hours carries EWMA base=$502!");
    assert_eq!(read_u64(&svm, &ewma_mkt, 112), 3_921_875, "After-hours STOXX/SOL = 502/128 = 3.921875!");

    // (e3) Bounded PushEwmaMark (op=3): reject non-admin, reject >5% jump (306), accept $520 (+3.58%),
    //      reject same-slot double push (308), then permissionless Crank reprices to 505.60/128 = 3.950!
    send_err(&mut svm, ix_push_ewma(attacker.pubkey(), 510 * POS_SCALE), &payer, &[&payer, &attacker], "PushEwmaMark rejects non-admin");
    send_err_custom(&mut svm, ix_push_ewma(lp.pubkey(), 550 * POS_SCALE), &payer, &[&payer, &lp], 306, "PushEwmaMark rejects >maxDevBps jump");
    let cu_push_ewma = send_ok(&mut svm, ix_push_ewma(lp.pubkey(), 520 * POS_SCALE), &payer, &[&payer, &lp]);
    assert_eq!(read_u64(&svm, &ewma_adp, 328), 505_600_000, "PushEwmaMark blended $502->$520 (20%) = $505.60!");
    send_err_custom(&mut svm, ix_push_ewma(lp.pubkey(), 510 * POS_SCALE), &payer, &[&payer, &lp], 308, "PushEwmaMark rejects same-slot double push");
    let mut c7: Clock = svm.get_sysvar(); c7.slot = s0 + 37; c7.unix_timestamp = 1_750_003_615; svm.set_sysvar(&c7);
    svm.set_account(sol_feed, Account { lamports: 10_000_000, data: make_chainlink_ocr2(8, 4, 2, s0 + 37, 12_800_000_000i128), owner: cl_prog_id, executable: false, rent_epoch: 0 }).unwrap();
    send_ok_assert_log(&mut svm, ix_ewma_crank(), &payer, &[&payer], "Program log: 0x1,");
    assert_eq!(read_u64(&svm, &ewma_mkt, 112), 3_950_000, "After-hours Crank after PushEwmaMark = 505.60/128 = 3.950!");

    // (e4) Market re-open: Pyth STOXX resumes live at $515.60 -> EWMA smoothly blends to $507.60!
    let mut c8: Clock = svm.get_sysvar(); c8.slot = s0 + 38; c8.unix_timestamp = 1_750_003_620; svm.set_sysvar(&c8);
    svm.set_account(stoxx_feed, Account { lamports: 10_000_000, data: make_pyth_v2(stoxx_fid, 51_560_000_000, 10_000_000, -8, 1_750_003_619, s0 + 38, 1), owner: pyth_prog_id, executable: false, rent_epoch: 0 }).unwrap();
    svm.set_account(sol_feed,   Account { lamports: 10_000_000, data: make_chainlink_ocr2(8, 4, 2, s0 + 38, 12_800_000_000i128), owner: cl_prog_id, executable: false, rent_epoch: 0 }).unwrap();
    send_ok_assert_log(&mut svm, ix_ewma_crank(), &payer, &[&payer], "Program log: 0x1,");
    assert_eq!(read_u64(&svm, &ewma_adp, 328), 507_600_000, "Market re-open smoothly blends EWMA $505.60->$515.60 = $507.60!");
    println!(
        "       Oracle Parsers: PythV2={} CU, ChainlinkOCR2={} CU, Switchboard128={} CU, Ratio(Pyth/CL)={} CU, EWMA(live={} / AH={} / push={} CU)",
        cu_pyth, cu_cl, cu_sb, cu_ratio, cu_ewma_live, cu_ewma_ah, cu_push_ewma
    );

    // 9B: Passive LP AMM Matcher CPI composition (Single-Signer Taker Open & Close!)
    let mtch_cfg = create_prog_acc(&mut svm, &matcher_prog, 128);
    let (lp_auth_pda, lp_bump) = Address::find_program_address(&[b"lpau", mtch_cfg.as_ref()], &matcher_prog);
    let lp_pfl = create_prog_acc(&mut svm, &prog_id, PFL_SIZE);
    let mut init_m_data = vec![0u8; 28];
    init_m_data[0] = 0;
    init_m_data[1] = lp_bump;
    init_m_data[4..12].copy_from_slice(&50u64.to_le_bytes());       // halfSpread = 50 bps (0.50%)
    init_m_data[12..20].copy_from_slice(&20u64.to_le_bytes());      // impact = 20 bps / unit
    init_m_data[20..28].copy_from_slice(&(10 * POS_SCALE).to_le_bytes()); // maxFillQty = 10
    send_ok(
        &mut svm,
        Instruction {
            program_id: matcher_prog,
            accounts: vec![
                AccountMeta::new(mtch_cfg, false),
                AccountMeta::new_readonly(lp.pubkey(), true),
                AccountMeta::new(dex, false),
                AccountMeta::new(lp_pfl, false),
                AccountMeta::new_readonly(lp_auth_pda, false),
                AccountMeta::new_readonly(prog_id, false),
            ],
            data: init_m_data,
        },
        &payer,
        &[&payer, &lp],
    );
    // Fund LP portfolio ($500) directly via core DepositCollateral? Note: DepositCollateral requires owner signature,
    // OR even cleaner: fund LP by depositing to a temporary owner or wait — let's check: lp_pfl.owner == lp_auth_pda!
    // So let's let LP fund via a direct zero-spread transfer or wait: in Suite 9B let's test LP deposit through
    // a tiny helper OR let LP trade against Alice? Wait: DepositCollateral requires `owner` signer (which is `lp_auth_pda`)!
    // Catching this in a real LiteSVM test is GOLD: `DepositCollateral` should allow ANY depositor (`depositor[S]`, NOT only `pfl.owner`!) to top up `pfl.capital`!
    // Let's verify that in Program.lean right now!
    let taker_kp = Keypair::new();
    svm.airdrop(&taker_kp.pubkey(), 10_000_000_000).unwrap();
    let taker_tok = create_tok_acc(&mut svm, &mint, &taker_kp.pubkey(), 1_000 * POS_SCALE);
    let taker_pfl = create_prog_acc(&mut svm, &prog_id, PFL_SIZE);
    send_ok(&mut svm, ix_init_portfolio(prog_id, dex, taker_pfl, taker_kp.pubkey()), &payer, &[&payer, &taker_kp]);
    send_ok(&mut svm, ix_deposit_collateral(prog_id, dex, taker_pfl, taker_kp.pubkey(), taker_tok, mint, dex_vault, TOKEN_PROGRAM_ID, 200 * POS_SCALE), &payer, &[&payer, &taker_kp]);
    // Permissionless deposit into PDA-owned LP portfolio (`lp` signs as depositor for `lp_pfl`!)
    send_ok(&mut svm, ix_deposit_collateral(prog_id, dex, lp_pfl, lp.pubkey(), lp_tok, mint, dex_vault, TOKEN_PROGRAM_ID, 500 * POS_SCALE), &payer, &[&payer, &lp]);

    let ix_fill = |mode: u8, taker_is_long: u8, qty: u64, limit_p: u64| {
        let mut d = vec![0u8; 19];
        d[0] = 2;
        d[1] = mode;
        d[2] = taker_is_long;
        d[3..11].copy_from_slice(&qty.to_le_bytes());
        d[11..19].copy_from_slice(&limit_p.to_le_bytes());
        Instruction {
            program_id: matcher_prog,
            accounts: vec![
                AccountMeta::new_readonly(mtch_cfg, false),
                AccountMeta::new(dex, false),
                AccountMeta::new(comp_mkt2, false),
                AccountMeta::new(lp_pfl, false),
                AccountMeta::new_readonly(lp_auth_pda, false),
                AccountMeta::new(taker_pfl, false),
                AccountMeta::new_readonly(taker_kp.pubkey(), true),
                AccountMeta::new_readonly(prog_id, false),
            ],
            data: d,
        }
    };
    // Slippage check: ask = $115 * (1 + 90bps) = $116.035 -> limit $115.50 REJECTED!
    send_err(&mut svm, ix_fill(0, 1, 2 * POS_SCALE, 115_500_000), &payer, &[&payer, &taker_kp], "Matcher rejects fill exceeding slippage limit");
    // Single-signer Taker OPEN Long 2.0 against passive LP (ZERO LP signature!)
    let cu_fill_open = send_ok(&mut svm, ix_fill(0, 1, 2 * POS_SCALE, 117 * POS_SCALE), &payer, &[&payer, &taker_kp]);
    let lp_cap_after_open = read_u64(&svm, &lp_pfl, 88);
    assert_eq!(lp_cap_after_open, 502_070_000, "LP must earn exact $2.07 spread on 2.0 fill at 90bps!");
    // Single-signer Taker CLOSE Long 2.0 against passive LP (ZERO LP signature!)
    let cu_fill_close = send_ok(&mut svm, ix_fill(1, 1, 2 * POS_SCALE, 117 * POS_SCALE), &payer, &[&payer, &taker_kp]);
    assert_eq!(read_u64(&svm, &comp_mkt2, 256), 0, "OI must return to 0 after single-signer close!");

    // LP owner withdraws $100 via Matcher::WithdrawLp (PDA signs percolator::WithdrawCollateral!)
    let mut wdr_lp_data = vec![0u8; 9];
    wdr_lp_data[0] = 3;
    wdr_lp_data[1..9].copy_from_slice(&(100 * POS_SCALE).to_le_bytes());
    let lp_tok_before = token_amount(&svm, &lp_tok);
    let cu_wdr_lp = send_ok(
        &mut svm,
        Instruction {
            program_id: matcher_prog,
            accounts: vec![
                AccountMeta::new_readonly(mtch_cfg, false),
                AccountMeta::new_readonly(lp.pubkey(), true),
                AccountMeta::new(dex, false),
                AccountMeta::new(lp_pfl, false),
                AccountMeta::new_readonly(lp_auth_pda, false),
                AccountMeta::new(lp_tok, false),
                AccountMeta::new_readonly(mint, false),
                AccountMeta::new(dex_vault, false),
                AccountMeta::new_readonly(TOKEN_PROGRAM_ID, false),
                AccountMeta::new_readonly(prog_id, false),
            ],
            data: wdr_lp_data,
        },
        &payer,
        &[&payer, &lp],
    );
    assert_eq!(token_amount(&svm, &lp_tok) - lp_tok_before, 100 * POS_SCALE);

    let all_mkts4 = vec![btc_mkt, eth_mkt, scam_mkt, comp_mkt, comp_mkt2];
    let all_pfls4 = vec![alice_pfl, bob_pfl, attacker_pfl, t2_pfl, dust_pfl, lp_pfl, taker_pfl];
    assert_dex_invariants(&svm, &dex, &dex_vault, &all_mkts4, &all_pfls4, "post-suite9-external-cpi");

    // 9C: Atomic [UpdateOracle/Crank + RefreshLeg(LP)] Anti-Reordering Bundle + K=4 Censored Envelope!
    //     1) Verifies atomic [Crank(SOL), RefreshLeg(SOL, LP), Crank(ETH), RefreshLeg(ETH, LP)]
    //        funds R_SOL in the SAME tx that moves the price, defeating adversarial-leader
    //        premature-liquidation reordering of a tight hedged spread!
    //     2) Verifies K=4 consecutive adverse oracle steps (maxMove=1%, mm=5%, liqFee=1%) with
    //        ZERO interleaved liquidations still liquidates with shortfall == 0 & I_m untouched!
    let (cu_crank_bundle, wire_crank_bundle, cu_k4_liq) = {
        let b_dex = create_prog_acc(&mut svm, &prog_id, DEX_SIZE);
        let (b_vault, b_bump) = derive_dex_vault(&prog_id, &b_dex);
        send_ok(&mut svm, ix_init_dex(prog_id, b_dex, dex_admin.pubkey(), mint, b_vault, fee_vault, TOKEN_PROGRAM_ID, SYSTEM_PROGRAM_ID, b_bump, 6, 0, SPL_TOKEN_RENT_MIN), &payer, &[&payer, &dex_admin]);
        let b_sol_mkt = create_prog_acc(&mut svm, &prog_id, MKT_SIZE);
        let b_eth_mkt = create_prog_acc(&mut svm, &prog_id, MKT_SIZE);
        let b_sol_adp = create_prog_acc(&mut svm, &adapter_prog, 352);
        let b_eth_adp = create_prog_acc(&mut svm, &adapter_prog, 352);
        let (b_sol_pda, b_sol_bump) = Address::find_program_address(&[b"orac", b_sol_adp.as_ref()], &adapter_prog);
        let (b_eth_pda, b_eth_bump) = Address::find_program_address(&[b"orac", b_eth_adp.as_ref()], &adapter_prog);
        let b_sol_feed = Keypair::new().pubkey();
        let b_eth_feed = Keypair::new().pubkey();
        let write_custom = |svm: &mut LiteSVM, faddr: Address, price: u64, slot: u64| {
            let mut d = vec![0u8; 32];
            d[0..4].copy_from_slice(&0x44454546u32.to_le_bytes());
            d[8..16].copy_from_slice(&price.to_le_bytes());
            d[16..24].copy_from_slice(&10_000u64.to_le_bytes());
            d[24..32].copy_from_slice(&slot.to_le_bytes());
            svm.set_account(faddr, Account { lamports: 10_000_000, data: d, owner: SYSTEM_PROGRAM_ID, executable: false, rent_epoch: 0 }).unwrap();
        };
        let b_sl0 = get_slot(&svm) + 1;
        set_slot(&mut svm, b_sl0);
        write_custom(&mut svm, b_sol_feed, 100 * POS_SCALE, b_sl0);
        write_custom(&mut svm, b_eth_feed, 100 * POS_SCALE, b_sl0);
        // maxMoveBps=100 (1%/slot), mmBps=500 (5%), liqFeeBps=100 (1%), maxStaleness=150 -> K=4 safe!
        send_ok(&mut svm, ix_create_market(prog_id, b_dex, b_sol_mkt, mint, b_sol_pda, lp.pubkey(), lp_tok, fee_vault, 100 * POS_SCALE, 20, 150, 0, 1000, 500, 100, 0, 100, 2500, 1_000_000 * POS_SCALE), &payer, &[&payer, &lp]);
        send_ok(&mut svm, ix_create_market(prog_id, b_dex, b_eth_mkt, mint, b_eth_pda, lp.pubkey(), lp_tok, fee_vault, 100 * POS_SCALE, 20, 150, 0, 1000, 500, 100, 0, 100, 2500, 1_000_000 * POS_SCALE), &payer, &[&payer, &lp]);
        let b_sol_ins = create_prog_acc(&mut svm, &prog_id, INS_SIZE);
        send_ok(&mut svm, ix_deposit_insurance(prog_id, b_dex, b_sol_mkt, b_sol_ins, lp.pubkey(), lp_tok, mint, b_vault, TOKEN_PROGRAM_ID, 500 * POS_SCALE), &payer, &[&payer, &lp]);
        for (adp, mkt, fd, bump) in [(b_sol_adp, b_sol_mkt, b_sol_feed, b_sol_bump), (b_eth_adp, b_eth_mkt, b_eth_feed, b_eth_bump)] {
            let mut d = vec![0u8; 28];
            d[0] = 0; d[1] = bump;
            d[4..12].copy_from_slice(&150u64.to_le_bytes());
            d[12..20].copy_from_slice(&100u64.to_le_bytes());
            send_ok(&mut svm, Instruction { program_id: adapter_prog, accounts: vec![
                AccountMeta::new(adp, false), AccountMeta::new_readonly(lp.pubkey(), true),
                AccountMeta::new_readonly(prog_id, false), AccountMeta::new_readonly(mkt, false),
                AccountMeta::new_readonly(fd, false),
            ], data: d }, &payer, &[&payer, &lp]);
        }

        // Hedged trader holds Long 10 SOL + Short 10 ETH ($200 IM, $100 MM) on $200 capital vs LP;
        // then withdraws $100? No, keep tight: Open Long 5 SOL + Short 5 ETH ($100 IM, $50 MM) on $100 cap,
        // PLUS a 2nd unhedged trader on SOL right at MM ($50 cap, Long 10 SOL? IM=$100 so open Long 5 SOL
        // with $50 cap after IM=50 -> price drops to MM=$25, then K=4 consecutive -1% steps!).
        let h_kp = Keypair::new(); let lp_kp = Keypair::new(); let u_kp = Keypair::new();
        let h_tok = create_tok_acc(&mut svm, &mint, &h_kp.pubkey(), 1_000 * POS_SCALE);
        let lp_b_tok = create_tok_acc(&mut svm, &mint, &lp_kp.pubkey(), 5_000 * POS_SCALE);
        let u_tok = create_tok_acc(&mut svm, &mint, &u_kp.pubkey(), 1_000 * POS_SCALE);
        let h_pfl = create_prog_acc(&mut svm, &prog_id, PFL_SIZE);
        let lp_b_pfl = create_prog_acc(&mut svm, &prog_id, PFL_SIZE);
        let u_pfl = create_prog_acc(&mut svm, &prog_id, PFL_SIZE);
        for (p, k, t, amt) in [(h_pfl, &h_kp, h_tok, 100 * POS_SCALE), (lp_b_pfl, &lp_kp, lp_b_tok, 2_000 * POS_SCALE), (u_pfl, &u_kp, u_tok, 100 * POS_SCALE)] {
            send_ok(&mut svm, ix_init_portfolio(prog_id, b_dex, p, k.pubkey()), &payer, &[&payer, k]);
            send_ok(&mut svm, ix_deposit_collateral(prog_id, b_dex, p, k.pubkey(), t, mint, b_vault, TOKEN_PROGRAM_ID, amt), &payer, &[&payer, k]);
        }
        send_ok(&mut svm, ix_trade(prog_id, b_dex, b_sol_mkt, h_pfl, h_kp.pubkey(), lp_b_pfl, lp_kp.pubkey(), 0, 5 * POS_SCALE), &payer, &[&payer, &h_kp, &lp_kp]);
        send_ok(&mut svm, ix_trade(prog_id, b_dex, b_eth_mkt, lp_b_pfl, lp_kp.pubkey(), h_pfl, h_kp.pubkey(), 0, 5 * POS_SCALE), &payer, &[&payer, &lp_kp, &h_kp]);
        // Unhedged trader U: Long 10 SOL ($1,000 notional, IM=$100, MM=$50) on $100 capital!
        send_ok(&mut svm, ix_trade(prog_id, b_dex, b_sol_mkt, u_pfl, u_kp.pubkey(), lp_b_pfl, lp_kp.pubkey(), 0, 10 * POS_SCALE), &payer, &[&payer, &u_kp, &lp_kp]);

        // Atomic Crank+LP Bundle on slot +1: both SOL and ETH jump +1% ($100 -> $101)!
        // Crank bot atomically executes [Crank(SOL), RefreshLeg(SOL, LP), Crank(ETH), RefreshLeg(ETH, LP)]
        // in ONE Solana tx so R_SOL is funded IMMEDIATELY in the same tx!
        set_slot(&mut svm, b_sl0 + 1);
        write_custom(&mut svm, b_sol_feed, 101 * POS_SCALE, b_sl0 + 1);
        write_custom(&mut svm, b_eth_feed, 101 * POS_SCALE, b_sl0 + 1);
        let ix_b_crank = |adp: Address, mkt: Address, fd: Address, pda: Address| Instruction {
            program_id: adapter_prog,
            accounts: vec![
                AccountMeta::new_readonly(adp, false), AccountMeta::new(mkt, false),
                AccountMeta::new_readonly(fd, false), AccountMeta::new_readonly(pda, false),
                AccountMeta::new_readonly(prog_id, false),
            ],
            data: vec![1],
        };
        let (cu_bndl, wire_bndl) = send_ixs_ok_measured(
            &mut svm,
            &[
                ix_b_crank(b_sol_adp, b_sol_mkt, b_sol_feed, b_sol_pda),
                ix_refresh_leg(prog_id, b_dex, b_sol_mkt, lp_b_pfl, false),
                ix_b_crank(b_eth_adp, b_eth_mkt, b_eth_feed, b_eth_pda),
                ix_refresh_leg(prog_id, b_dex, b_eth_mkt, lp_b_pfl, false),
            ],
            &payer,
            &[&payer],
        );
        // Hedged trader's SOL gain (+$5) immediately covers ETH loss (-$5) -> capital == $100,
        // and adversarial keeper liquidation attempt on ETH is REJECTED!
        send_ixs_ok(&mut svm, &[
            ix_refresh_leg(prog_id, b_dex, b_sol_mkt, h_pfl, false),
            ix_refresh_leg(prog_id, b_dex, b_eth_mkt, h_pfl, false),
        ], &payer, &[&payer]);
        assert_eq!(read_u64(&svm, &h_pfl, 88), 100 * POS_SCALE, "Atomic Crank+LP bundle preserved exact $100 hedged capital!");
        send_err(&mut svm, ix_liquidate(prog_id, b_dex, b_eth_mkt, h_pfl, keeper_tok, mint, b_vault, TOKEN_PROGRAM_ID), &payer, &[&payer], "Hedged trader cannot be liquidated after atomic Crank+LP bundle");

        // Now test K=4 consecutive censored liquidation slots on unhedged U (Long 10 SOL)!
        // First push SOL down 5% ($101 -> ~$95) so U sits right near MM ($50 capital vs ~$47.5 MM),
        // then run K=4 consecutive -1% oracle slots WITHOUT liquidating U, then liquidate on honest slot!
        let mut p_sol = 101 * POS_SCALE;
        for st in 2..=6u64 {
            set_slot(&mut svm, b_sl0 + st);
            p_sol = (p_sol * 99) / 100;
            write_custom(&mut svm, b_sol_feed, p_sol, b_sl0 + st);
            send_ok(&mut svm, ix_b_crank(b_sol_adp, b_sol_mkt, b_sol_feed, b_sol_pda), &payer, &[&payer]);
        }
        // Refresh U right at MM boundary (~$51 capital vs ~$48 MM): still healthy!
        send_ok(&mut svm, ix_refresh_leg(prog_id, b_dex, b_sol_mkt, u_pfl, false), &payer, &[&payer]);
        let ins_before_k4 = read_u64(&svm, &b_sol_mkt, 224);
        // K=4 consecutive censored oracle slots (-1%/slot, ZERO liquidations!)
        for st in 7..=10u64 {
            set_slot(&mut svm, b_sl0 + st);
            p_sol = (p_sol * 99) / 100;
            write_custom(&mut svm, b_sol_feed, p_sol, b_sl0 + st);
            send_ok(&mut svm, ix_b_crank(b_sol_adp, b_sol_mkt, b_sol_feed, b_sol_pda), &payer, &[&payer]);
        }
        // Honest leader arrives on slot +10 and liquidates U: ZERO bad debt & I_SOL bit-for-bit untouched!
        let cu_k4 = send_ok(&mut svm, ix_liquidate(prog_id, b_dex, b_sol_mkt, u_pfl, keeper_tok, mint, b_vault, TOKEN_PROGRAM_ID), &payer, &[&payer]);
        assert_eq!(read_u64(&svm, &b_sol_mkt, 224), ins_before_k4, "K=4 censored oracle slots produced ZERO bad debt (I_SOL untouched)!");
        assert_dex_invariants(&svm, &b_dex, &b_vault, &[b_sol_mkt, b_eth_mkt], &[h_pfl, lp_b_pfl, u_pfl], "post-9C-atomic-bundle-and-k4");
        (cu_bndl, wire_bndl, cu_k4)
    };
    println!(
        "[PASS] Suite 9: External CPI (adapter={} B crank={} CU, matcher={} B open/close/wdr={}/{}/{} CU) + Atomic Crank+LP Bundle ({} CU, {} B) + K=4 Censored Liq ({} CU, 0 bad debt)!",
        adapter_elf.len(), cu_crank, matcher_elf.len(), cu_fill_open, cu_fill_close, cu_wdr_lp, cu_crank_bundle, wire_crank_bundle, cu_k4_liq
    );

    // =========================================================================
    // SUITE 10: CORE HARDENING + FAIR TRANSPARENT LIQUIDATIONS (NO TTP!)
    //   10a. Unbounded maxStaleness / exitWindow / warmupSlots!=0 REJECTED!
    //   10b. Trade(mode=1) execPrice cross-margin bypass REJECTED!
    //   10c. Partial Liquidation + Permissionless Counterparty Takeover (ZERO ADL!) + Gradual Fee!
    // =========================================================================
    // 10a. Unbounded parameter DoS rejections
    let bad_mkt2 = create_prog_acc(&mut svm, &prog_id, MKT_SIZE);
    send_err(&mut svm, ix_create_market(prog_id, dex, bad_mkt2, mint, btc_oracle.pubkey(), alice.pubkey(), alice_tok, fee_vault,
        100 * POS_SCALE, 300_000, 50, 0, 1000, 500, 100, 0, 400, 2500, 1_000_000 * POS_SCALE),
        &payer, &[&payer, &alice], "exitWindow > MAX_EXIT_WINDOW rejected");
    send_err(&mut svm, ix_create_market(prog_id, dex, bad_mkt2, mint, btc_oracle.pubkey(), alice.pubkey(), alice_tok, fee_vault,
        100 * POS_SCALE, 20, 50_000, 0, 1000, 500, 100, 0, 400, 2500, 1_000_000 * POS_SCALE),
        &payer, &[&payer, &alice], "maxStaleness > MAX_STALENESS rejected");
    send_err(&mut svm, ix_create_market(prog_id, dex, bad_mkt2, mint, btc_oracle.pubkey(), alice.pubkey(), alice_tok, fee_vault,
        100 * POS_SCALE, 20, 50, 1, 1000, 500, 100, 0, 400, 2500, 1_000_000 * POS_SCALE),
        &payer, &[&payer, &alice], "non-zero warmupSlots rejected");

    // 10b + 10c on fresh fair-liq market `fair_mkt` ($100, IM=10%, MM=5%, liqFee=1%, maxMove=4%)
    let fair_mkt = create_prog_acc(&mut svm, &prog_id, MKT_SIZE);
    let fair_orc = Keypair::new();
    let victim = Keypair::new();
    let hlp_lp = Keypair::new();
    let cparty = Keypair::new();
    for kp in [&fair_orc, &victim, &hlp_lp, &cparty] {
        svm.airdrop(&kp.pubkey(), 10_000_000_000).unwrap();
    }
    let vic_tok = create_tok_acc(&mut svm, &mint, &victim.pubkey(), 1_000 * POS_SCALE);
    let hlp_tok = create_tok_acc(&mut svm, &mint, &hlp_lp.pubkey(), 2_000 * POS_SCALE);
    let cp_tok  = create_tok_acc(&mut svm, &mint, &cparty.pubkey(), 2_000 * POS_SCALE);
    let vic_pfl = create_prog_acc(&mut svm, &prog_id, PFL_SIZE);
    let hlp_pfl = create_prog_acc(&mut svm, &prog_id, PFL_SIZE);
    let cp_pfl  = create_prog_acc(&mut svm, &prog_id, PFL_SIZE);

    send_ok(&mut svm, ix_create_market(prog_id, dex, fair_mkt, mint, fair_orc.pubkey(), lp.pubkey(), lp_tok, fee_vault,
        100 * POS_SCALE, 20, 50, 0, 1000, 500, 100, 0, 400, 2500, 1_000_000 * POS_SCALE),
        &payer, &[&payer, &lp]);
    send_ok(&mut svm, ix_init_portfolio(prog_id, dex, vic_pfl, victim.pubkey()), &payer, &[&payer, &victim]);
    send_ok(&mut svm, ix_init_portfolio(prog_id, dex, hlp_pfl, hlp_lp.pubkey()), &payer, &[&payer, &hlp_lp]);
    send_ok(&mut svm, ix_init_portfolio(prog_id, dex, cp_pfl,  cparty.pubkey()), &payer, &[&payer, &cparty]);
    send_ok(&mut svm, ix_deposit_collateral(prog_id, dex, vic_pfl, victim.pubkey(), vic_tok, mint, dex_vault, TOKEN_PROGRAM_ID, 100 * POS_SCALE), &payer, &[&payer, &victim]);
    send_ok(&mut svm, ix_deposit_collateral(prog_id, dex, hlp_pfl, hlp_lp.pubkey(), hlp_tok, mint, dex_vault, TOKEN_PROGRAM_ID, 500 * POS_SCALE), &payer, &[&payer, &hlp_lp]);
    send_ok(&mut svm, ix_deposit_collateral(prog_id, dex, cp_pfl,  cparty.pubkey(), cp_tok,  mint, dex_vault, TOKEN_PROGRAM_ID, 500 * POS_SCALE), &payer, &[&payer, &cparty]);

    // Victim opens Long 10.0 @ $100 vs Counterparty Short 10.0
    send_ok(&mut svm, ix_trade(prog_id, dex, fair_mkt, vic_pfl, victim.pubkey(), cp_pfl, cparty.pubkey(), 0, 10 * POS_SCALE),
        &payer, &[&payer, &victim, &cparty]);

    // 10b. Verify Trade(mode=1) execPrice spread CANNOT drain payer below remaining totalMm!
    let s_fair = get_slot(&svm) + 1;
    set_slot(&mut svm, s_fair);
    send_ok(&mut svm, ix_update_oracle(prog_id, fair_mkt, fair_orc.pubkey(), 96_500_000, 0, 0), &payer, &[&payer, &fair_orc]);
    set_slot(&mut svm, s_fair + 1);
    send_ok(&mut svm, ix_update_oracle(prog_id, fair_mkt, fair_orc.pubkey(), 94_600_000, 0, 0), &payer, &[&payer, &fair_orc]);
    send_err(&mut svm, ix_trade_ext(prog_id, dex, fair_mkt, vic_pfl, victim.pubkey(), cp_pfl, cparty.pubkey(), 1, POS_SCALE, 98_200_000),
        &payer, &[&payer, &victim, &cparty], "Trade(mode=1) execPrice draining below totalMm rejected");

    // 10c. Fair Partial Liquidation + Permissionless Takeover (**ZERO ADL ON INNOCENT COUNTERPARTY!**)
    let hlp_tok_0 = token_amount(&svm, &hlp_tok);
    let cu_part_take = send_ok(
        &mut svm,
        ix_liquidate_ext(prog_id, dex, fair_mkt, vic_pfl, hlp_tok, mint, dex_vault, TOKEN_PROGRAM_ID,
            1, 4 * POS_SCALE, Some((hlp_pfl, hlp_lp.pubkey()))),
        &payer,
        &[&payer, &hlp_lp],
    );
    let fee_paid = token_amount(&svm, &hlp_tok) - hlp_tok_0;
    let max_part_fee = (4 * 94_600_000u64) / 100;
    assert!(fee_paid > 0 && fee_paid < max_part_fee, "Gradual deficit fee ({}) must be strictly < maxFee ({})!", fee_paid, max_part_fee);
    assert_eq!(read_u64(&svm, &vic_pfl, LEG_HEADER + 48), 6 * POS_SCALE, "Victim must retain 6.0 units after partial liquidation!");
    assert_eq!(read_u64(&svm, &hlp_pfl, LEG_HEADER + 48), 4 * POS_SCALE, "Liquidator must hold 4.0 taken-over units!");
    assert_eq!(read_u64(&svm, &fair_mkt, 256), 10 * POS_SCALE, "OI must stay 10.0 (takeover, no OI destroy)!");
    assert_eq!(read_u64(&svm, &fair_mkt, 288), ADL_ONE, "adlLong MUST remain ADL_ONE (ZERO ADL)!");
    assert_eq!(read_u64(&svm, &fair_mkt, 296), ADL_ONE, "adlShort MUST remain ADL_ONE (ZERO ADL)!");
    send_err(&mut svm, ix_liquidate(prog_id, dex, fair_mkt, vic_pfl, keeper_tok, mint, dex_vault, TOKEN_PROGRAM_ID),
        &payer, &[&payer], "Victim is healthy after partial liquidation!");

    let all_mkts5 = vec![btc_mkt, eth_mkt, scam_mkt, comp_mkt, comp_mkt2, fair_mkt];
    let all_pfls5 = vec![alice_pfl, bob_pfl, attacker_pfl, t2_pfl, dust_pfl, lp_pfl, taker_pfl, vic_pfl, hlp_pfl, cp_pfl];
    assert_dex_invariants(&svm, &dex, &dex_vault, &all_mkts5, &all_pfls5, "post-suite10-fair-liq");
    println!(
        "[PASS] Suite 10: Core Hardening + Partial Permissionless Takeover ({} CU, gradual fee={} < max={}, ZERO ADL!)",
        cu_part_take, fee_paid, max_part_fee
    );

    // =========================================================================
    // SUITE 11: WORST-CASE 8-LEG (`MAX_LEGS = 8`) CU EXHAUSTION + A1 / A2 / B4
    //   Tests EVERY worst-case actor role on a FULL 8-market, 8-leg portfolio:
    //   1. A1 Selective-Liquidation Attack on an 8-leg hedged spread (REJECTED!)
    //   2. USERS: Atomic [8x RefreshLeg + WithdrawCollateral], Atomic [8x RefreshLeg + Trade],
    //             Double-8-Leg Trade (both parties holding 8 legs = 16 legs total!)
    //   3. B4 Position Hand-Off: Trade(mode=2 Long->Long) & Trade(mode=3 Short->Short) on 8-leg portfolio
    //   4. LIQUIDATION KEEPERS:
    //        - Worst-case 8-leg Tier-3 fallback: Atomic [7x RefreshLeg + Liquidate(mode=0)]
    //        - A2 Post-ADL Recovery: Post-ADL Trade(mode=0) open + Post-ADL 8-leg Takeover (mode=1)
    //          where BOTH victim (8 legs) AND liquidator (8 legs) are maxed out!
    //   5. CRANKS: 8-market UpdateOracle batch, 8-market OracleAdapter CPI crank,
    //              8-market WindDown -> ForceClosePair -> ClearDeadLeg -> ResolveMarket sweep!
    //   Verifies BOTH Solana CU budget (<= 200,000 default CU!) AND 1,232B legacy UDP packet limit!
    // =========================================================================
    let w_dex = create_prog_acc(&mut svm, &prog_id, DEX_SIZE);
    let (w_vault, w_bump) = derive_dex_vault(&prog_id, &w_dex);
    send_ok(
        &mut svm,
        ix_init_dex(prog_id, w_dex, dex_admin.pubkey(), mint, w_vault, fee_vault, TOKEN_PROGRAM_ID, SYSTEM_PROGRAM_ID, w_bump, 6, 0, SPL_TOKEN_RENT_MIN),
        &payer,
        &[&payer, &dex_admin],
    );

    let mut w_slot = get_slot(&svm) + 10;
    set_slot(&mut svm, w_slot);

    let mut w_mkts = Vec::new();
    let w_orc_shared = Keypair::new();
    svm.airdrop(&w_orc_shared.pubkey(), 10_000_000_000).unwrap();
    let mut w_mkt_pairs = Vec::new();
    let mut w_ins = Vec::new();
    let mut w_adps = Vec::new();
    let mut w_orac_pdas = Vec::new();
    let mut w_feeds = Vec::new();

    for i in 0..MAX_LEGS {
        let mkt = create_prog_acc(&mut svm, &prog_id, MKT_SIZE);
        let ins = create_prog_acc(&mut svm, &prog_id, INS_SIZE);
        // Market i: $100, exitWindow=10, maxStaleness=200, IM=10%, MM=5%, liqFee=1%, tradeFee=0, maxMove=4%, insDraw=25%
        send_ok(
            &mut svm,
            ix_create_market(prog_id, w_dex, mkt, mint, w_orc_shared.pubkey(), lp.pubkey(), lp_tok, fee_vault,
                100 * POS_SCALE, 10, 200, 0, 1000, 500, 100, 0, 400, 2500, 1_000_000 * POS_SCALE),
            &payer,
            &[&payer, &lp],
        );
        send_ok(
            &mut svm,
            ix_deposit_insurance(prog_id, w_dex, mkt, ins, lp.pubkey(), lp_tok, mint, w_vault, TOKEN_PROGRAM_ID, 500 * POS_SCALE),
            &payer,
            &[&payer, &lp],
        );
        // Also wire an OracleAdapter CPI feed on a second set of adapters? We can rotate oracleAuth later for crank test!
        let adp = create_prog_acc(&mut svm, &adapter_prog, 352);
        let (opda, obump) = Address::find_program_address(&[b"orac", adp.as_ref()], &adapter_prog);
        let feed = Keypair::new().pubkey();
        let mut fd = vec![0u8; 32];
        fd[0..4].copy_from_slice(&0x44454546u32.to_le_bytes());
        fd[8..16].copy_from_slice(&(100 * POS_SCALE).to_le_bytes());
        fd[16..24].copy_from_slice(&50_000u64.to_le_bytes());
        fd[24..32].copy_from_slice(&w_slot.to_le_bytes());
        svm.set_account(feed, Account { lamports: 10_000_000, data: fd, owner: SYSTEM_PROGRAM_ID, executable: false, rent_epoch: 0 }).unwrap();
        let mut iad = vec![0u8; 28];
        iad[0] = 0;
        iad[1] = obump;
        iad[4..12].copy_from_slice(&50u64.to_le_bytes());
        iad[12..20].copy_from_slice(&100u64.to_le_bytes());
        iad[20..28].copy_from_slice(&0u64.to_le_bytes());
        send_ok(
            &mut svm,
            Instruction {
                program_id: adapter_prog,
                accounts: vec![
                    AccountMeta::new(adp, false),
                    AccountMeta::new_readonly(lp.pubkey(), true),
                    AccountMeta::new_readonly(prog_id, false),
                    AccountMeta::new_readonly(mkt, false),
                    AccountMeta::new_readonly(feed, false),
                ],
                data: iad,
            },
            &payer,
            &[&payer, &lp],
        );

        w_mkts.push(mkt);
        w_mkt_pairs.push(((i + 1) as u64, mkt));
        w_ins.push(ins);
        w_adps.push(adp);
        w_orac_pdas.push(opda);
        w_feeds.push(feed);
    }

    // Create 4 portfolios on w_dex:
    //   u_pfl (User A — 8 legs!), c_pfl (Counterparty B — 8 legs!),
    //   k_pfl (Liquidation Keeper / HLP — 8 legs!), d_pfl (Helper Counterparty for keeper legs & post-ADL open)
    let w_user = Keypair::new();
    let w_cp   = Keypair::new();
    let w_keep = Keypair::new();
    let w_aux  = Keypair::new();
    for kp in [&w_user, &w_cp, &w_keep, &w_aux] {
        svm.airdrop(&kp.pubkey(), 10_000_000_000).unwrap();
    }
    let wu_tok = create_tok_acc(&mut svm, &mint, &w_user.pubkey(), 50_000 * POS_SCALE);
    let wc_tok = create_tok_acc(&mut svm, &mint, &w_cp.pubkey(),   50_000 * POS_SCALE);
    let wk_tok = create_tok_acc(&mut svm, &mint, &w_keep.pubkey(), 50_000 * POS_SCALE);
    let wa_tok = create_tok_acc(&mut svm, &mint, &w_aux.pubkey(),  50_000 * POS_SCALE);

    let wu_pfl = create_prog_acc(&mut svm, &prog_id, PFL_SIZE);
    let wc_pfl = create_prog_acc(&mut svm, &prog_id, PFL_SIZE);
    let wk_pfl = create_prog_acc(&mut svm, &prog_id, PFL_SIZE);
    let wa_pfl = create_prog_acc(&mut svm, &prog_id, PFL_SIZE);
    let w_all_pfls = vec![wu_pfl, wc_pfl, wk_pfl, wa_pfl];

    for (pfl, kp, tok, cap) in [
        (wu_pfl, &w_user, wu_tok, 200 * POS_SCALE), // $200 capital -> 8 legs x $200 notional = $1600 gross ($160 IM, $80 MM)!
        (wc_pfl, &w_cp,   wc_tok, 5_000 * POS_SCALE),
        (wk_pfl, &w_keep, wk_tok, 5_000 * POS_SCALE),
        (wa_pfl, &w_aux,  wa_tok, 5_000 * POS_SCALE),
    ] {
        send_ok(&mut svm, ix_init_portfolio(prog_id, w_dex, pfl, kp.pubkey()), &payer, &[&payer, kp]);
        send_ok(&mut svm, ix_deposit_collateral(prog_id, w_dex, pfl, kp.pubkey(), tok, mint, w_vault, TOKEN_PROGRAM_ID, cap), &payer, &[&payer, kp]);
    }

    // Open ALL 8 LEGS on User A (Long mkts 0..4, Short mkts 4..8, qty = 2.0 each -> $1600 notional, IM=$160, MM=$80)
    // AND ALL 8 LEGS on Counterparty B (opposite side on all 8 markets)!
    for i in 0..MAX_LEGS {
        if i < 4 {
            send_ok(&mut svm, ix_trade(prog_id, w_dex, w_mkts[i], wu_pfl, w_user.pubkey(), wc_pfl, w_cp.pubkey(), 0, 2 * POS_SCALE),
                &payer, &[&payer, &w_user, &w_cp]);
        } else {
            send_ok(&mut svm, ix_trade(prog_id, w_dex, w_mkts[i], wc_pfl, w_cp.pubkey(), wu_pfl, w_user.pubkey(), 0, 2 * POS_SCALE),
                &payer, &[&payer, &w_cp, &w_user]);
        }
    }
    // Also populate Keeper (wk_pfl) with 7 legs on mkts 1..8 (so taking over mkt 0 fills ALL 8 LEGS of Keeper!)
    for i in 1..MAX_LEGS {
        send_ok(&mut svm, ix_trade(prog_id, w_dex, w_mkts[i], wk_pfl, w_keep.pubkey(), wa_pfl, w_aux.pubkey(), 0, POS_SCALE),
            &payer, &[&payer, &w_keep, &w_aux]);
    }
    assert_eq!(read_u8(&svm, &wu_pfl, 4), 8, "User A must hold ALL 8 legs!");
    assert_eq!(read_u8(&svm, &wc_pfl, 4), 8, "Counterparty B must hold ALL 8 legs!");
    assert_eq!(read_u8(&svm, &wk_pfl, 4), 7, "Keeper must hold 7 legs before takeover!");
    assert_dex_invariants(&svm, &w_dex, &w_vault, &w_mkts, &w_all_pfls, "suite11-8leg-open");

    // 11.1 CRANK WORST-CASE: Batch 8x UpdateOracle in ONE single Solana tx!
    w_slot += 1;
    set_slot(&mut svm, w_slot);
    let orc_ixs: Vec<Instruction> = (0..MAX_LEGS)
        .map(|i| ix_update_oracle(prog_id, w_mkts[i], w_orc_shared.pubkey(), 103_500_000, 0, 0))
        .collect();
    let (cu_crank_8orc, wire_8orc) = send_ixs_ok_measured(&mut svm, &orc_ixs, &payer, &[&payer, &w_orc_shared]);
    assert!(cu_crank_8orc < 200_000 && wire_8orc <= 1232, "8x UpdateOracle batch exceeded limits: {} CU, {} B", cu_crank_8orc, wire_8orc);

    // 11.2 A1 SELECTIVE LIQUIDATION ATTACK ON 8-LEG HEDGED SPREAD:
    //   All 8 markets rose +3.5% ($100 -> $103.50): User A won +$28 on mkts 0..3 and lost -$28 on mkts 4..7!
    //   First Counterparty B refreshes its losing legs (mkts 0..3) so R_m is funded for User A's winners.
    let cp_ref_win: Vec<Instruction> = (0..4).map(|i| ix_refresh_leg(prog_id, w_dex, w_mkts[i], wc_pfl, false)).collect();
    send_ixs_ok(&mut svm, &cp_ref_win, &payer, &[&payer]);
    //   Attack A1a: bare Liquidate(mkt 4, wu_pfl) WITHOUT refreshing other 7 legs -> REJECTED (`stalePortfolioLeg`)!
    send_err(&mut svm, ix_liquidate(prog_id, w_dex, w_mkts[4], wu_pfl, wk_tok, mint, w_vault, TOKEN_PROGRAM_ID),
        &payer, &[&payer], "A1: Selective single-leg liquidation on 8-leg hedged portfolio MUST fail");
    //   Attack A1b: Atomic [7x RefreshLeg(mkts 0..3, 5..7) + Liquidate(mkt 4)] -> REJECTED (`positionHealthy`)!
    let mut a1_ixs: Vec<Instruction> = (0..MAX_LEGS).filter(|&i| i != 4)
        .map(|i| ix_refresh_leg(prog_id, w_dex, w_mkts[i], wu_pfl, false)).collect();
    a1_ixs.push(ix_liquidate(prog_id, w_dex, w_mkts[4], wu_pfl, wk_tok, mint, w_vault, TOKEN_PROGRAM_ID));
    send_ixs_err(&mut svm, &a1_ixs, &payer, &[&payer], "A1: Net-healthy 8-leg hedged portfolio cannot be liquidated");

    // 11.3 USER WORST-CASE 8-LEG ATOMIC WITHDRAW: [8x RefreshLeg(wu_pfl) + WithdrawCollateral($10)] in ONE tx!
    w_slot += 1;
    set_slot(&mut svm, w_slot);
    let mut wdr8_ixs: Vec<Instruction> = (0..MAX_LEGS).map(|i| ix_refresh_leg(prog_id, w_dex, w_mkts[i], wu_pfl, false)).collect();
    wdr8_ixs.push(ix_withdraw_collateral(prog_id, w_dex, wu_pfl, w_user.pubkey(), wu_tok, mint, w_vault, TOKEN_PROGRAM_ID, 10 * POS_SCALE));
    let (cu_user_8wdr, wire_user_8wdr) = send_ixs_ok_measured(&mut svm, &wdr8_ixs, &payer, &[&payer, &w_user]);
    assert!(cu_user_8wdr < 200_000 && wire_user_8wdr <= 1232, "8-leg atomic Withdraw exceeded limits: {} CU, {} B", cu_user_8wdr, wire_user_8wdr);

    // 11.4 USER WORST-CASE 8-LEG ATOMIC TRADE:
    //   (a) Single-tx [8x RefreshLeg(wu_pfl) + Trade(wu_pfl vs wa_pfl)] — single-sided 8-leg atomic tx!
    //   (b) Double-8-leg worst case (BOTH wu_pfl AND wc_pfl hold 8 legs = 16 legs total):
    //       Check whether 17 ixs fits in 1 legacy tx (1,232B MTU) and measure both 1-tx & 2-tx same-slot CU!
    w_slot += 1;
    set_slot(&mut svm, w_slot);
    let mut trd16_ixs: Vec<Instruction> = (0..MAX_LEGS).map(|i| ix_refresh_leg(prog_id, w_dex, w_mkts[i], wu_pfl, false)).collect();
    trd16_ixs.extend((0..MAX_LEGS).map(|i| ix_refresh_leg(prog_id, w_dex, w_mkts[i], wc_pfl, false)));
    trd16_ixs.push(ix_trade(prog_id, w_dex, w_mkts[0], wu_pfl, w_user.pubkey(), wc_pfl, w_cp.pubkey(), 0, POS_SCALE / 10));
    let (cu_user_16trd, wire_user_16trd) = send_ixs_ok_measured(&mut svm, &trd16_ixs, &payer, &[&payer, &w_user, &w_cp]);
    assert!(cu_user_16trd < 200_000 && wire_user_16trd <= 1232, "Double-8-leg atomic Trade exceeded limits: {} CU, {} B", cu_user_16trd, wire_user_16trd);

    // 11.5 B4 POSITION HAND-OFF (`Trade` mode=2 Long->Long & mode=3 Short->Short) ON 8-LEG PORTFOLIO!
    //   User A (8 legs) hands off 0.5 Long on mkt 0 to Keeper (who currently has 7 legs -> becomes 8 legs!)
    //   with bounded execPrice spread ($104.00 vs $103.50 mark = +$0.50/unit -> Keeper pays $0.25 to User A).
    w_slot += 1;
    set_slot(&mut svm, w_slot);
    let m0_oi_0 = read_u64(&svm, &w_mkts[0], 256);
    let m0_rl_0 = read_u64(&svm, &w_mkts[0], 272);
    let m0_adl_0 = read_u64(&svm, &w_mkts[0], 288);
    let mut ho_ixs: Vec<Instruction> = (1..MAX_LEGS).map(|i| ix_refresh_leg(prog_id, w_dex, w_mkts[i], wk_pfl, false)).collect();
    ho_ixs.push(ix_trade_ext(prog_id, w_dex, w_mkts[0], wu_pfl, w_user.pubkey(), wk_pfl, w_keep.pubkey(), 2, POS_SCALE / 2, 104 * POS_SCALE));
    let (cu_handoff_l, wire_handoff_l) = send_ixs_ok_measured(&mut svm, &ho_ixs, &payer, &[&payer, &w_user, &w_keep]);
    assert_eq!(read_u64(&svm, &w_mkts[0], 256), m0_oi_0, "B4 Long->Long handoff must leave oiLong bit-for-bit invariant!");
    assert_eq!(read_u64(&svm, &w_mkts[0], 272), m0_rl_0, "B4 Long->Long handoff must leave rawBasisLong invariant!");
    assert_eq!(read_u64(&svm, &w_mkts[0], 288), m0_adl_0, "B4 Long->Long handoff must leave adlLong invariant!");
    assert_eq!(read_u8(&svm, &wk_pfl, 4), 8, "Keeper now holds ALL 8 LEGS!");
    //   Also test B4 mode=3 (Short->Short handoff on mkt 4 from User A to Aux)!
    let m4_oi_0 = read_u64(&svm, &w_mkts[4], 264);
    let mut ho_s_ixs: Vec<Instruction> = (1..MAX_LEGS).map(|i| ix_refresh_leg(prog_id, w_dex, w_mkts[i], wa_pfl, false)).collect();
    ho_s_ixs.push(ix_trade_ext(prog_id, w_dex, w_mkts[4], wu_pfl, w_user.pubkey(), wa_pfl, w_aux.pubkey(), 3, POS_SCALE / 2, 103 * POS_SCALE));
    let (cu_handoff_s, _) = send_ixs_ok_measured(&mut svm, &ho_s_ixs, &payer, &[&payer, &w_user, &w_aux]);
    assert_eq!(read_u64(&svm, &w_mkts[4], 264), m4_oi_0, "B4 Short->Short handoff must leave oiShort bit-for-bit invariant!");
    assert_dex_invariants(&svm, &w_dex, &w_vault, &w_mkts, &w_all_pfls, "suite11-post-b4-handoff");

    // 11.6 LIQUIDATION KEEPER WORST-CASE (8-LEG VICTIM + 8-LEG LIQUIDATOR + A2 POST-ADL RECOVERY!):
    //   Crash mkt 0 (User A is Long 1.6) AND pump mkts 4..7 (User A is Short) over 12 slots so User A is genuinely underwater!
    let mut p0 = 103_500_000u64;
    let mut p_hi = 103_500_000u64;
    for _ in 0..12 {
        w_slot += 1;
        set_slot(&mut svm, w_slot);
        p0 = p0 - (p0 * 39) / 1000;
        p_hi = p_hi + (p_hi * 39) / 1000;
        let mut step_ixs = vec![ix_update_oracle(prog_id, w_mkts[0], w_orc_shared.pubkey(), p0, 0, 0)];
        for i in 4..MAX_LEGS {
            step_ixs.push(ix_update_oracle(prog_id, w_mkts[i], w_orc_shared.pubkey(), p_hi, 0, 0));
        }
        send_ixs_ok(&mut svm, &step_ixs, &payer, &[&payer, &w_orc_shared]);
    }
    //   11.6a Worst-Case 8-Leg Tier-3 Fallback Liquidation (`mode = 0`, partial 0.8 on mkt 0 -> triggers partial ADL!)
    //   Atomic ONE-tx: [7x RefreshLeg(wu_pfl, mkts 1..8) + Liquidate(mode=0, reqQty=0.8, mkt 0, wu_pfl)]!
    let mut liq0_ixs: Vec<Instruction> = (1..MAX_LEGS).map(|i| ix_refresh_leg(prog_id, w_dex, w_mkts[i], wu_pfl, false)).collect();
    liq0_ixs.push(ix_liquidate_ext(prog_id, w_dex, w_mkts[0], wu_pfl, wk_tok, mint, w_vault, TOKEN_PROGRAM_ID, 0, 800_000, None));
    let (cu_liq8_fallback, wire_liq8_fallback) = send_ixs_ok_measured(&mut svm, &liq0_ixs, &payer, &[&payer]);
    assert!(cu_liq8_fallback < 200_000 && wire_liq8_fallback <= 1232, "8-leg fallback Liquidate exceeded limits: {} CU, {} B", cu_liq8_fallback, wire_liq8_fallback);
    //   Verify partial ADL occurred on mkt 0 (`0 < oiShort < rawBasisShort`, `adlShort < ADL_ONE`)!
    let m0_oi_adl = read_u64(&svm, &w_mkts[0], 264);
    let m0_rs_adl = read_u64(&svm, &w_mkts[0], 280);
    let m0_adls   = read_u64(&svm, &w_mkts[0], 296);
    assert!(m0_oi_adl > 0 && m0_oi_adl < m0_rs_adl && m0_adls < ADL_ONE,
        "Expected partial ADL on mkt 0: oi={}, rawS={}, adlS={}", m0_oi_adl, m0_rs_adl, m0_adls);

    //   11.6b A2 POST-ADL RECOVERY #1: Post-ADL `Trade(mode = 0)` new open on partially-ADL'd mkt 0!
    //   Refresh Aux & Keeper legs, then open 0.5 new OI on partially-ADL'd mkt 0!
    w_slot += 1;
    set_slot(&mut svm, w_slot);
    let mut post_adl_open_ixs: Vec<Instruction> = (0..MAX_LEGS).map(|i| ix_refresh_leg(prog_id, w_dex, w_mkts[i], wk_pfl, false)).collect();
    post_adl_open_ixs.extend((1..MAX_LEGS).map(|i| ix_refresh_leg(prog_id, w_dex, w_mkts[i], wa_pfl, false)));
    post_adl_open_ixs.push(ix_trade(prog_id, w_dex, w_mkts[0], wk_pfl, w_keep.pubkey(), wa_pfl, w_aux.pubkey(), 0, 500_000));
    let (cu_post_adl_open, wire_post_adl_open) = send_ixs_ok_measured(&mut svm, &post_adl_open_ixs, &payer, &[&payer, &w_keep, &w_aux]);
    let m0_adls_after_open = read_u64(&svm, &w_mkts[0], 296);
    assert!(m0_adls_after_open <= m0_adls, "A2 post-ADL open must NEVER inflate adlShort ({} > {})!", m0_adls_after_open, m0_adls);
    assert_eq!(read_u64(&svm, &w_mkts[0], 256), m0_oi_adl + 500_000, "A2 post-ADL open increased OI cleanly!");

    //   11.6c A2 POST-ADL RECOVERY #2 + WORST-CASE DOUBLE-8-LEG TAKEOVER (`mode = 1`):
    //   BOTH Victim (wu_pfl, 8 legs) AND Liquidator (wk_pfl, 8 legs!) hold ALL 8 LEGS on a partially-ADL'd market!
    //   Test ONE SINGLE ATOMIC TX: [7x RefreshLeg(wu_pfl) + 7x RefreshLeg(wk_pfl) + Liquidate(mode=1, mkt 0)]!
    w_slot += 1;
    set_slot(&mut svm, w_slot);
    let m0_oi_pre = read_u64(&svm, &w_mkts[0], 256);
    let m0_rl_pre = read_u64(&svm, &w_mkts[0], 272);
    let m0_rs_pre = read_u64(&svm, &w_mkts[0], 280);
    let m0_adll_pre = read_u64(&svm, &w_mkts[0], 288);
    let m0_adls_pre = read_u64(&svm, &w_mkts[0], 296);
    let mut take16_ixs: Vec<Instruction> = (1..MAX_LEGS).map(|i| ix_refresh_leg(prog_id, w_dex, w_mkts[i], wu_pfl, false)).collect();
    take16_ixs.extend((1..MAX_LEGS).map(|i| ix_refresh_leg(prog_id, w_dex, w_mkts[i], wk_pfl, false)));
    take16_ixs.push(ix_liquidate_ext(prog_id, w_dex, w_mkts[0], wu_pfl, wk_tok, mint, w_vault, TOKEN_PROGRAM_ID,
        1, 0, Some((wk_pfl, w_keep.pubkey()))));
    let (cu_liq16_takeover, wire_liq16_takeover) = send_ixs_ok_measured(&mut svm, &take16_ixs, &payer, &[&payer, &w_keep]);
    assert!(cu_liq16_takeover < 200_000 && wire_liq16_takeover <= 1232, "Double-8-leg Takeover exceeded limits: {} CU, {} B", cu_liq16_takeover, wire_liq16_takeover);
    //   Verify Post-ADL Takeover preserved ALL market OI/rawBasis/ADL fields BIT-FOR-BIT!
    assert_eq!(read_u64(&svm, &w_mkts[0], 256), m0_oi_pre, "Post-ADL Takeover must preserve oiLong!");
    assert_eq!(read_u64(&svm, &w_mkts[0], 272), m0_rl_pre, "Post-ADL Takeover must preserve rawBasisLong!");
    assert_eq!(read_u64(&svm, &w_mkts[0], 280), m0_rs_pre, "Post-ADL Takeover must preserve rawBasisShort!");
    assert_eq!(read_u64(&svm, &w_mkts[0], 288), m0_adll_pre, "Post-ADL Takeover must preserve adlLong!");
    assert_eq!(read_u64(&svm, &w_mkts[0], 296), m0_adls_pre, "Post-ADL Takeover must preserve adlShort!");

    // 11.7 CRANK WORST-CASE: Rotate all 8 markets to OracleAdapter CPI & crank all 8 markets via CPI!
    for i in 0..MAX_LEGS {
        send_ok(&mut svm, ix_update_market_auth(prog_id, w_mkts[i], lp.pubkey(), 1, w_orac_pdas[i]), &payer, &[&payer, &lp]);
    }
    w_slot += 1;
    set_slot(&mut svm, w_slot);
    let mut cpi_crank_max_cu = 0u64;
    let mut cpi_crank_total_cu = 0u64;
    for i in 0..MAX_LEGS {
        let cur_p = read_u64(&svm, &w_mkts[i], 112);
        let mut fd = vec![0u8; 32];
        fd[0..4].copy_from_slice(&0x44454546u32.to_le_bytes());
        fd[8..16].copy_from_slice(&((cur_p * 101) / 100).to_le_bytes());
        fd[16..24].copy_from_slice(&50_000u64.to_le_bytes());
        fd[24..32].copy_from_slice(&w_slot.to_le_bytes());
        svm.set_account(w_feeds[i], Account { lamports: 10_000_000, data: fd, owner: SYSTEM_PROGRAM_ID, executable: false, rent_epoch: 0 }).unwrap();
        let cu = send_ok(
            &mut svm,
            Instruction {
                program_id: adapter_prog,
                accounts: vec![
                    AccountMeta::new_readonly(w_adps[i], false),
                    AccountMeta::new(w_mkts[i], false),
                    AccountMeta::new_readonly(w_feeds[i], false),
                    AccountMeta::new_readonly(w_orac_pdas[i], false),
                    AccountMeta::new_readonly(prog_id, false),
                ],
                data: vec![1],
            },
            &payer,
            &[&payer],
        );
        cpi_crank_max_cu = cpi_crank_max_cu.max(cu);
        cpi_crank_total_cu += cu;
    }

    // 11.8 CRANK WORST-CASE WIND-DOWN SWEEP ACROSS ALL 8 MARKETS:
    //   StartWindDown on all 8 -> advance exitWindow -> ForceClosePair + ClearDeadLeg + ResolveMarket!
    for i in 0..MAX_LEGS {
        send_ok(&mut svm, ix_start_wind_down(prog_id, w_mkts[i], lp.pubkey()), &payer, &[&payer, &lp]);
    }
    w_slot += 15;
    set_slot(&mut svm, w_slot);
    let mut max_fc_cu = 0u64;
    let mut max_res_cu = 0u64;
    for i in 0..MAX_LEGS {
        // Force-close all (Long, Short) pairs among the 4 portfolios until OI == 0
        for _round in 0..6 {
            if read_u64(&svm, &w_mkts[i], 256) == 0 { break; }
            for &p_l in &w_all_pfls {
                for &p_s in &w_all_pfls {
                    if p_l == p_s { continue; }
                    if let Ok(cu) = send_ixs_try(&mut svm, &[ix_force_close_pair(prog_id, w_dex, w_mkts[i], p_l, p_s)], &payer, &[&payer]) {
                        max_fc_cu = max_fc_cu.max(cu);
                    }
                }
            }
        }
        // Clear any remaining post-ADL dead legs on market i
        for &p in &w_all_pfls {
            let _ = send_ixs_try(&mut svm, &[ix_clear_dead_leg(prog_id, w_dex, w_mkts[i], p)], &payer, &[&payer]);
        }
        let cu_res = send_ok(&mut svm, ix_resolve_market(prog_id, w_dex, w_mkts[i]), &payer, &[&payer]);
        max_res_cu = max_res_cu.max(cu_res);
        // Claim any resolved PnL legs
        for &p in &w_all_pfls {
            let _ = send_ixs_try(&mut svm, &[ix_claim_resolved(prog_id, w_dex, w_mkts[i], p)], &payer, &[&payer]);
        }
    }
    assert_dex_invariants(&svm, &w_dex, &w_vault, &w_mkts, &w_all_pfls, "suite11-post-8mkt-resolve");
    println!("[PASS] Suite 11: Worst-Case 8-Leg CU Exhaustion + A1 / A2 / B4 Verified (ZERO CU/MTU Exhaustion!):");
    println!("       User 8-leg Withdraw  [8xRef + Wdr]            : {:>6} CU | {:>4} B / 1232 B (default budget 200k)", cu_user_8wdr, wire_user_8wdr);
    println!("       User 16-leg Trade    [16xRef + Trade]         : {:>6} CU | {:>4} B / 1232 B", cu_user_16trd, wire_user_16trd);
    println!("       B4 Position Hand-Off [7xRef + L->L / S->S]    : {:>6} / {:>5} CU | {:>4} B (OI/ADL bit-for-bit invariant!)", cu_handoff_l, cu_handoff_s, wire_handoff_l);
    println!("       Keeper 8-leg Liq(m0) [7xRef + Fallback]       : {:>6} CU | {:>4} B / 1232 B", cu_liq8_fallback, wire_liq8_fallback);
    println!("       A2 Post-ADL Open     [15xRef + Trade(m0)]     : {:>6} CU | {:>4} B / 1232 B (adl monotone!)", cu_post_adl_open, wire_post_adl_open);
    println!("       Keeper 16-leg Liq(m1)[14xRef + Takeover(ADL)] : {:>6} CU | {:>4} B / 1232 B", cu_liq16_takeover, wire_liq16_takeover);
    println!("       Crank 8-mkt Batch    [8x UpdateOracle 1 tx]   : {:>6} CU | {:>4} B / 1232 B", cu_crank_8orc, wire_8orc);
    println!("       Crank 8-mkt CPI/Sweep[OracleAdapter max/8x]   : {:>6} / {:>5} CU | ForceClose max={} CU, Resolve max={} CU", cpi_crank_max_cu, cpi_crank_total_cu, max_fc_cu, max_res_cu);
    println!("==================================================================================");
    println!("  ALL 11 PERCOLATOR-LEAN VERIFICATION + 8-LEG STRESS + A1/A2/B4 + FUZZ SUITES PASSED 100%!");
    println!("==================================================================================");
}
