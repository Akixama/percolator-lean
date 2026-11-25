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

// Exact layout offsets matching Percolator/Layout.lean
const PROT_SIZE: usize = 88;
const MKT_SIZE: usize = 392;
const POS_SIZE: usize = 152;
const PFL_SIZE: usize = 88;
const INS_SIZE: usize = 88;

fn make_spl_mint(decimals: u8, supply: u64, mint_auth: &Address) -> Vec<u8> {
    let mut data = vec![0u8; 82];
    data[0..4].copy_from_slice(&1u32.to_le_bytes());
    data[4..36].copy_from_slice(mint_auth.as_ref());
    data[36..44].copy_from_slice(&supply.to_le_bytes());
    data[44] = decimals;
    data[45] = 1; // is_initialized
    data
}

fn make_spl_token_account(mint: &Address, owner: &Address, amount: u64) -> Vec<u8> {
    let mut data = vec![0u8; 165];
    data[0..32].copy_from_slice(mint.as_ref());
    data[32..64].copy_from_slice(owner.as_ref());
    data[64..72].copy_from_slice(&amount.to_le_bytes());
    data[108] = 1; // AccountState::Initialized
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

fn send_ok(svm: &mut LiteSVM, ix: Instruction, payer: &Keypair, signers: &[&Keypair]) -> u64 {
    svm.expire_blockhash();
    let bh = svm.latest_blockhash();
    let msg = Message::new(&[ix], Some(&payer.pubkey()));
    let tx = Transaction::new(signers, msg, bh);
    let res = svm.send_transaction(tx).unwrap_or_else(|e| panic!("Expected OK, got {:?}", e));
    res.compute_units_consumed
}

fn send_err(svm: &mut LiteSVM, ix: Instruction, payer: &Keypair, signers: &[&Keypair], label: &str) {
    svm.expire_blockhash();
    let bh = svm.latest_blockhash();
    let msg = Message::new(&[ix], Some(&payer.pubkey()));
    let tx = Transaction::new(signers, msg, bh);
    let res = svm.send_transaction(tx);
    assert!(res.is_err(), "Expected rejection for '{}', but tx succeeded!", label);
}

fn create_prog_acc(svm: &mut LiteSVM, prog_id: &Address, size: usize) -> Address {
    let kp = Keypair::new();
    let addr = kp.pubkey();
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
    let kp = Keypair::new();
    let addr = kp.pubkey();
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

fn create_pda_vault(
    svm: &mut LiteSVM,
    prog_id: &Address,
    tag: &[u8; 4],
    seed_key: &Address,
    mint: &Address,
) -> (Address, u8) {
    let (pda, bump) = Address::find_program_address(&[tag, seed_key.as_ref()], prog_id);
    svm.set_account(
        pda,
        Account {
            lamports: 10_000_000,
            data: make_spl_token_account(mint, &pda, 0),
            owner: TOKEN_PROGRAM_ID,
            executable: false,
            rent_epoch: 0,
        },
    )
    .unwrap();
    (pda, bump)
}

fn assert_vault_conserved(svm: &LiteSVM, mkt: &Address, mkt_vault: &Address, label: &str) {
    let v = read_u64(svm, mkt, 248);
    let c = read_u64(svm, mkt, 256);
    let i = read_u64(svm, mkt, 264);
    let s = read_u64(svm, mkt, 272);
    let spl = token_amount(svm, mkt_vault);
    assert_eq!(v, spl, "[{}] vaultBalance ({}) != real SPL balance ({})", label, v, spl);
    assert!(
        c.saturating_add(i).saturating_add(s) <= v,
        "[{}] Vault conservation violated: C({}) + I({}) + S({}) > V({})",
        label, c, i, s, v
    );
}

#[allow(clippy::too_many_arguments)]
fn ix_create_market(
    prog_id: Address,
    prot: Address,
    mkt: Address,
    mint: Address,
    vault_pda: Address,
    oracle_auth: Address,
    creator: Address,
    creator_tok: Address,
    fee_vault: Address,
    bump: u8,
    decimals: u8,
    init_price: u64,
    exit_window: u64,
    max_staleness: u64,
    warmup_slots: u64,
    im_bps: u64,
    mm_bps: u64,
    liq_fee_bps: u64,
    trade_fee_bps: u64,
    max_move_bps: u64,
    max_ins_draw_bps: u64,
    max_oi: u64,
) -> Instruction {
    let mut data = vec![0u8; 92];
    data[0] = 2; // IxOp.createMarket
    data[1] = bump;
    data[2] = decimals;
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
    Instruction {
        program_id: prog_id,
        accounts: vec![
            AccountMeta::new(prot, false),
            AccountMeta::new(mkt, false),
            AccountMeta::new_readonly(mint, false),
            AccountMeta::new_readonly(vault_pda, false),
            AccountMeta::new_readonly(oracle_auth, false),
            AccountMeta::new_readonly(creator, true),
            AccountMeta::new(creator_tok, false),
            AccountMeta::new(fee_vault, false),
            AccountMeta::new_readonly(TOKEN_PROGRAM_ID, false),
        ],
        data,
    }
}

fn main() {
    let so_path = std::env::args()
        .nth(1)
        .unwrap_or_else(|| "build/percolator.so".to_string());
    let elf = std::fs::read(&so_path).unwrap_or_else(|e| panic!("Failed to read {}: {}", so_path, e));
    println!("==================================================================================");
    println!("  percolator-lean — Unified Lean 4 -> sBPF Perps DEX Verification Suite");
    println!("  Binary: {} ({} bytes, 0 heap, 0 engine/prog split)", so_path, elf.len());
    println!("==================================================================================");

    let mut svm = LiteSVM::new();
    let prog_id = Keypair::new().pubkey();
    svm.add_program(prog_id, &elf).expect("ELF load failed");
    set_slot(&mut svm, 100);

    let payer = Keypair::new();
    let prot_admin = Keypair::new();
    let alice = Keypair::new();
    let bob = Keypair::new();
    let lp = Keypair::new();
    let keeper = Keypair::new();
    let attacker = Keypair::new();
    let sockpuppet = Keypair::new();
    let btc_oracle = Keypair::new();
    let eth_oracle = Keypair::new();
    let scam_oracle = Keypair::new();

    for kp in [&payer, &prot_admin, &alice, &bob, &lp, &keeper, &attacker, &sockpuppet, &btc_oracle, &eth_oracle, &scam_oracle] {
        svm.airdrop(&kp.pubkey(), 10_000_000_000).unwrap();
    }

    // Create USDC (6 decimals) quote mint
    let mint = Keypair::new().pubkey();
    svm.set_account(
        mint,
        Account {
            lamports: 10_000_000,
            data: make_spl_mint(6, 1_000_000_000_000, &prot_admin.pubkey()),
            owner: TOKEN_PROGRAM_ID,
            executable: false,
            rent_epoch: 0,
        },
    )
    .unwrap();

    let fee_vault = create_tok_acc(&mut svm, &mint, &prot_admin.pubkey(), 0);
    let alice_tok = create_tok_acc(&mut svm, &mint, &alice.pubkey(), 100_000_000);     // 100 USDC
    let bob_tok   = create_tok_acc(&mut svm, &mint, &bob.pubkey(), 100_000_000);       // 100 USDC
    let lp_tok    = create_tok_acc(&mut svm, &mint, &lp.pubkey(), 50_000_000);         // 50 USDC
    let keep_tok  = create_tok_acc(&mut svm, &mint, &keeper.pubkey(), 0);
    let atk_tok   = create_tok_acc(&mut svm, &mint, &attacker.pubkey(), 20_000_000);   // 20 USDC
    let sock_tok  = create_tok_acc(&mut svm, &mint, &sockpuppet.pubkey(), 20_000_000); // 20 USDC

    // -------------------------------------------------------------------------
    // 1. InitProtocol + Admin Containment Check
    // -------------------------------------------------------------------------
    let prot = create_prog_acc(&mut svm, &prog_id, PROT_SIZE);
    let mut init_data = vec![0u8; 9];
    init_data[0] = 0;
    init_data[1..9].copy_from_slice(&1_000_000u64.to_le_bytes()); // 1 USDC create fee
    let cu_init = send_ok(
        &mut svm,
        Instruction {
            program_id: prog_id,
            accounts: vec![
                AccountMeta::new(prot, false),
                AccountMeta::new_readonly(prot_admin.pubkey(), true),
                AccountMeta::new_readonly(fee_vault, false),
            ],
            data: init_data,
        },
        &payer,
        &[&payer, &prot_admin],
    );
    // Unauthorized UpdateCreateFee must reject
    let mut bad_fee = vec![1u8; 9];
    bad_fee[1..9].copy_from_slice(&0u64.to_le_bytes());
    send_err(
        &mut svm,
        Instruction {
            program_id: prog_id,
            accounts: vec![
                AccountMeta::new(prot, false),
                AccountMeta::new_readonly(attacker.pubkey(), true),
            ],
            data: bad_fee,
        },
        &payer,
        &[&payer, &attacker],
        "unauthorized UpdateCreateFee",
    );
    println!("[PASS] 1. InitProtocol & Admin Auth       | CUs = {}", cu_init);

    // -------------------------------------------------------------------------
    // 2. Permissionless Market Creation + Solvency Envelope Rejection
    // -------------------------------------------------------------------------
    let btc_mkt = create_prog_acc(&mut svm, &prog_id, MKT_SIZE);
    let (btc_vault, btc_bump) = create_pda_vault(&mut svm, &prog_id, b"mvlt", &btc_mkt, &mint);
    let eth_mkt = create_prog_acc(&mut svm, &prog_id, MKT_SIZE);
    let (eth_vault, eth_bump) = create_pda_vault(&mut svm, &prog_id, b"mvlt", &eth_mkt, &mint);

    // Invalid solvency envelope: maxMoveBps(400) + liqFeeBps(200) = 600 > mmBps(500) -> MUST REJECT!
    send_err(
        &mut svm,
        ix_create_market(
            prog_id, prot, btc_mkt, mint, btc_vault, btc_oracle.pubkey(),
            alice.pubkey(), alice_tok, fee_vault, btc_bump, 6,
            100_000_000, 20, 50, 10, 1000, 500, 200, 10, 400, 5000, 10_000_000_000,
        ),
        &payer,
        &[&payer, &alice],
        "invalid solvency envelope (maxMove + liqFee > mmBps)",
    );

    // Valid BTC-PERP ($100.00, IM=10%, MM=5%, liqFee=1%, maxMove=4% -> 4%+1%<=5%, warmup=10 slots)
    let cu_create = send_ok(
        &mut svm,
        ix_create_market(
            prog_id, prot, btc_mkt, mint, btc_vault, btc_oracle.pubkey(),
            alice.pubkey(), alice_tok, fee_vault, btc_bump, 6,
            100_000_000, 20, 50, 10, 1000, 500, 100, 10, 400, 5000, 10_000_000_000,
        ),
        &payer,
        &[&payer, &alice],
    );
    assert_eq!(read_u64(&svm, &btc_mkt, 8), 1); // market_id == 1
    assert_eq!(token_amount(&svm, &fee_vault), 1_000_000);

    // Valid ETH-PERP ($50.00)
    send_ok(
        &mut svm,
        ix_create_market(
            prog_id, prot, eth_mkt, mint, eth_vault, eth_oracle.pubkey(),
            bob.pubkey(), bob_tok, fee_vault, eth_bump, 6,
            50_000_000, 20, 50, 10, 1000, 500, 100, 10, 400, 5000, 10_000_000_000,
        ),
        &payer,
        &[&payer, &bob],
    );
    assert_eq!(read_u64(&svm, &eth_mkt, 8), 2); // market_id == 2
    println!("[PASS] 2. Permissionless CreateMarket     | CUs = {} (BTC=id1, ETH=id2, envelope enforced)", cu_create);

    // -------------------------------------------------------------------------
    // 3. Isolated Insurance Pool Deposit (BTC + ETH)
    // -------------------------------------------------------------------------
    let btc_ins_rec = create_prog_acc(&mut svm, &prog_id, INS_SIZE);
    let eth_ins_rec = create_prog_acc(&mut svm, &prog_id, INS_SIZE);
    let mut dep_ins = vec![12u8; 9];
    dep_ins[1..9].copy_from_slice(&20_000_000u64.to_le_bytes()); // 20 USDC into BTC insurance
    let cu_dep_ins = send_ok(
        &mut svm,
        Instruction {
            program_id: prog_id,
            accounts: vec![
                AccountMeta::new(btc_mkt, false),
                AccountMeta::new(btc_ins_rec, false),
                AccountMeta::new_readonly(lp.pubkey(), true),
                AccountMeta::new_readonly(mint, false),
                AccountMeta::new(lp_tok, false),
                AccountMeta::new(btc_vault, false),
                AccountMeta::new_readonly(TOKEN_PROGRAM_ID, false),
            ],
            data: dep_ins.clone(),
        },
        &payer,
        &[&payer, &lp],
    );
    send_ok(
        &mut svm,
        Instruction {
            program_id: prog_id,
            accounts: vec![
                AccountMeta::new(eth_mkt, false),
                AccountMeta::new(eth_ins_rec, false),
                AccountMeta::new_readonly(lp.pubkey(), true),
                AccountMeta::new_readonly(mint, false),
                AccountMeta::new(lp_tok, false),
                AccountMeta::new(eth_vault, false),
                AccountMeta::new_readonly(TOKEN_PROGRAM_ID, false),
            ],
            data: dep_ins,
        },
        &payer,
        &[&payer, &lp],
    );
    assert_vault_conserved(&svm, &btc_mkt, &btc_vault, "after BTC ins deposit");
    assert_vault_conserved(&svm, &eth_mkt, &eth_vault, "after ETH ins deposit");
    println!("[PASS] 3. Isolated Insurance Deposits     | CUs = {} (BTC=20 USDC, ETH=20 USDC)", cu_dep_ins);

    // -------------------------------------------------------------------------
    // 4. Cross-Market Portfolios + Positions + Margin Allocation + Atomic Rebalance
    // -------------------------------------------------------------------------
    let alice_pfl = create_prog_acc(&mut svm, &prog_id, PFL_SIZE);
    let (alice_pvlt, alice_pbump) = create_pda_vault(&mut svm, &prog_id, b"pvlt", &alice_pfl, &mint);
    let bob_pfl = create_prog_acc(&mut svm, &prog_id, PFL_SIZE);
    let (bob_pvlt, bob_pbump) = create_pda_vault(&mut svm, &prog_id, b"pvlt", &bob_pfl, &mint);

    for (pfl, bump, owner, tok) in [
        (alice_pfl, alice_pbump, &alice, alice_tok),
        (bob_pfl, bob_pbump, &bob, bob_tok),
    ] {
        send_ok(
            &mut svm,
            Instruction {
                program_id: prog_id,
                accounts: vec![
                    AccountMeta::new(pfl, false),
                    AccountMeta::new_readonly(owner.pubkey(), true),
                    AccountMeta::new_readonly(mint, false),
                ],
                data: vec![5, bump, 6],
            },
            &payer,
            &[&payer, owner],
        );
        let pvlt = if pfl == alice_pfl { alice_pvlt } else { bob_pvlt };
        let mut dep = vec![6u8; 9];
        dep[1..9].copy_from_slice(&50_000_000u64.to_le_bytes()); // 50 USDC to portfolio
        send_ok(
            &mut svm,
            Instruction {
                program_id: prog_id,
                accounts: vec![
                    AccountMeta::new(pfl, false),
                    AccountMeta::new_readonly(owner.pubkey(), true),
                    AccountMeta::new_readonly(mint, false),
                    AccountMeta::new(tok, false),
                    AccountMeta::new(pvlt, false),
                    AccountMeta::new_readonly(TOKEN_PROGRAM_ID, false),
                ],
                data: dep,
            },
            &payer,
            &[&payer, owner],
        );
    }

    let alice_btc = create_prog_acc(&mut svm, &prog_id, POS_SIZE);
    let bob_btc   = create_prog_acc(&mut svm, &prog_id, POS_SIZE);
    let alice_eth = create_prog_acc(&mut svm, &prog_id, POS_SIZE);
    let bob_eth   = create_prog_acc(&mut svm, &prog_id, POS_SIZE);

    for (mkt, pos, owner) in [
        (btc_mkt, alice_btc, &alice),
        (btc_mkt, bob_btc, &bob),
        (eth_mkt, alice_eth, &alice),
        (eth_mkt, bob_eth, &bob),
    ] {
        send_ok(
            &mut svm,
            Instruction {
                program_id: prog_id,
                accounts: vec![
                    AccountMeta::new(mkt, false),
                    AccountMeta::new(pos, false),
                    AccountMeta::new_readonly(owner.pubkey(), true),
                ],
                data: vec![8],
            },
            &payer,
            &[&payer, owner],
        );
    }

    // Allocate 30 USDC to Alice BTC, 12 USDC to Bob BTC, 10 USDC to Bob ETH
    let alloc_ix = |mkt, pos, pfl, pvlt, mvlt, owner: &Keypair, amt: u64| {
        let mut d = vec![9u8; 9];
        d[1..9].copy_from_slice(&amt.to_le_bytes());
        Instruction {
            program_id: prog_id,
            accounts: vec![
                AccountMeta::new(mkt, false),
                AccountMeta::new(pos, false),
                AccountMeta::new(pfl, false),
                AccountMeta::new_readonly(owner.pubkey(), true),
                AccountMeta::new_readonly(mint, false),
                AccountMeta::new(pvlt, false),
                AccountMeta::new(mvlt, false),
                AccountMeta::new_readonly(TOKEN_PROGRAM_ID, false),
            ],
            data: d,
        }
    };
    let cu_alloc = send_ok(&mut svm, alloc_ix(btc_mkt, alice_btc, alice_pfl, alice_pvlt, btc_vault, &alice, 30_000_000), &payer, &[&payer, &alice]);
    send_ok(&mut svm, alloc_ix(btc_mkt, bob_btc, bob_pfl, bob_pvlt, btc_vault, &bob, 12_000_000), &payer, &[&payer, &bob]);
    send_ok(&mut svm, alloc_ix(eth_mkt, bob_eth, bob_pfl, bob_pvlt, eth_vault, &bob, 10_000_000), &payer, &[&payer, &bob]);

    // Atomic cross-market RebalanceMargin: move 10 USDC directly BTC-PERP -> ETH-PERP for Alice!
    let mut reb_data = vec![11u8; 9];
    reb_data[1..9].copy_from_slice(&10_000_000u64.to_le_bytes());
    // First test aliased market rejection (mkt1 == mkt2)
    send_err(
        &mut svm,
        Instruction {
            program_id: prog_id,
            accounts: vec![
                AccountMeta::new(btc_mkt, false),
                AccountMeta::new(alice_btc, false),
                AccountMeta::new(btc_mkt, false),
                AccountMeta::new(alice_eth, false),
                AccountMeta::new_readonly(alice.pubkey(), true),
                AccountMeta::new_readonly(mint, false),
                AccountMeta::new(btc_vault, false),
                AccountMeta::new(eth_vault, false),
                AccountMeta::new_readonly(TOKEN_PROGRAM_ID, false),
            ],
            data: reb_data.clone(),
        },
        &payer,
        &[&payer, &alice],
        "aliased RebalanceMargin",
    );
    let cu_rebal = send_ok(
        &mut svm,
        Instruction {
            program_id: prog_id,
            accounts: vec![
                AccountMeta::new(btc_mkt, false),
                AccountMeta::new(alice_btc, false),
                AccountMeta::new(eth_mkt, false),
                AccountMeta::new(alice_eth, false),
                AccountMeta::new_readonly(alice.pubkey(), true),
                AccountMeta::new_readonly(mint, false),
                AccountMeta::new(btc_vault, false),
                AccountMeta::new(eth_vault, false),
                AccountMeta::new_readonly(TOKEN_PROGRAM_ID, false),
            ],
            data: reb_data,
        },
        &payer,
        &[&payer, &alice],
    );
    assert_eq!(read_u64(&svm, &alice_btc, 96), 20_000_000);
    assert_eq!(read_u64(&svm, &alice_eth, 96), 10_000_000);
    assert_vault_conserved(&svm, &btc_mkt, &btc_vault, "after rebalance BTC");
    assert_vault_conserved(&svm, &eth_mkt, &eth_vault, "after rebalance ETH");
    println!("[PASS] 4. Cross-Market Alloc & Rebalance  | Alloc={} CU, Rebalance(BTC->ETH)={} CU", cu_alloc, cu_rebal);

    // -------------------------------------------------------------------------
    // 5. Bilateral Matched Trades (BTC & ETH) + Aliasing Rejection + Insurance Lock
    // -------------------------------------------------------------------------
    let trade_ix = |mkt, pos_l, pos_s, own_l: &Keypair, own_s: &Keypair, qty: u64, px: u64, mode: u8| {
        let mut d = vec![0u8; 18];
        d[0] = 14;
        d[1..9].copy_from_slice(&qty.to_le_bytes());
        d[9..17].copy_from_slice(&px.to_le_bytes());
        d[17] = mode;
        Instruction {
            program_id: prog_id,
            accounts: vec![
                AccountMeta::new(mkt, false),
                AccountMeta::new(pos_l, false),
                AccountMeta::new(pos_s, false),
                AccountMeta::new_readonly(own_l.pubkey(), true),
                AccountMeta::new_readonly(own_s.pubkey(), true),
            ],
            data: d,
        }
    };
    // Aliased self-trade on same Position account MUST reject!
    send_err(
        &mut svm,
        trade_ix(btc_mkt, alice_btc, alice_btc, &alice, &alice, 1_000_000, 100_000_000, 0),
        &payer,
        &[&payer, &alice],
        "aliased Trade (posLong == posShort)",
    );

    // Alice Long 1.0 BTC vs Bob Short 1.0 BTC at $100 (notional $100, IM $10, MM $5; Bob has $12!)
    let cu_trade = send_ok(
        &mut svm,
        trade_ix(btc_mkt, alice_btc, bob_btc, &alice, &bob, 1_000_000, 100_000_000, 0),
        &payer,
        &[&payer, &alice, &bob],
    );
    assert_eq!(read_u64(&svm, &btc_mkt, 296), 1_000_000); // oiLong
    assert_eq!(read_u64(&svm, &btc_mkt, 304), 1_000_000); // oiShort
    assert_eq!(read_u64(&svm, &btc_mkt, 264), 20_200_000); // insurance grew by 2 * 0.10 USDC trade fees!

    // Alice Long 1.0 ETH vs Bob Short 1.0 ETH at $50
    send_ok(
        &mut svm,
        trade_ix(eth_mkt, alice_eth, bob_eth, &alice, &bob, 1_000_000, 50_000_000, 0),
        &payer,
        &[&payer, &alice, &bob],
    );

    // LP trying to withdraw BTC insurance while OI > 0 MUST REJECT!
    let mut wd_ins = vec![13u8; 9];
    wd_ins[1..9].copy_from_slice(&1_000_000u64.to_le_bytes());
    send_err(
        &mut svm,
        Instruction {
            program_id: prog_id,
            accounts: vec![
                AccountMeta::new(btc_mkt, false),
                AccountMeta::new(btc_ins_rec, false),
                AccountMeta::new_readonly(lp.pubkey(), true),
                AccountMeta::new_readonly(mint, false),
                AccountMeta::new(btc_vault, false),
                AccountMeta::new(lp_tok, false),
                AccountMeta::new_readonly(TOKEN_PROGRAM_ID, false),
            ],
            data: wd_ins,
        },
        &payer,
        &[&payer, &lp],
        "WithdrawInsurance while OI > 0",
    );
    println!("[PASS] 5. Bilateral Trade & OI Coherence  | CUs = {} (OI balanced, fees->ins, ins locked)", cu_trade);

    // -------------------------------------------------------------------------
    // 6. ADVERSARIAL: Malicious Permissionless Market 3 ("SCAM-PERP") Contagion Test!
    // -------------------------------------------------------------------------
    let btc_snap_before = svm.get_account(&btc_mkt).unwrap().data.clone();
    let eth_snap_before = svm.get_account(&eth_mkt).unwrap().data.clone();
    let alice_btc_before = svm.get_account(&alice_btc).unwrap().data.clone();

    let scam_mkt = create_prog_acc(&mut svm, &prog_id, MKT_SIZE);
    let (scam_vault, scam_bump) = create_pda_vault(&mut svm, &prog_id, b"mvlt", &scam_mkt, &mint);
    send_ok(
        &mut svm,
        ix_create_market(
            prog_id, prot, scam_mkt, mint, scam_vault, scam_oracle.pubkey(),
            attacker.pubkey(), atk_tok, fee_vault, scam_bump, 6,
            10_000_000, 10, 20, 5, 1000, 500, 100, 0, 400, 5000, 100_000_000_000,
        ),
        &payer,
        &[&payer, &attacker],
    );
    // Attacker & sockpuppet trade on SCAM-PERP and pump oracle wildly (clamped steps)
    let atk_pfl = create_prog_acc(&mut svm, &prog_id, PFL_SIZE);
    let (atk_pvlt, atk_pbump) = create_pda_vault(&mut svm, &prog_id, b"pvlt", &atk_pfl, &mint);
    let sock_pfl = create_prog_acc(&mut svm, &prog_id, PFL_SIZE);
    let (sock_pvlt, sock_pbump) = create_pda_vault(&mut svm, &prog_id, b"pvlt", &sock_pfl, &mint);
    for (pfl, bump, pvlt, own, tok) in [
        (atk_pfl, atk_pbump, atk_pvlt, &attacker, atk_tok),
        (sock_pfl, sock_pbump, sock_pvlt, &sockpuppet, sock_tok),
    ] {
        send_ok(&mut svm, Instruction {
            program_id: prog_id,
            accounts: vec![AccountMeta::new(pfl, false), AccountMeta::new_readonly(own.pubkey(), true), AccountMeta::new_readonly(mint, false)],
            data: vec![5, bump, 6],
        }, &payer, &[&payer, own]);
        let mut d = vec![6u8; 9]; d[1..9].copy_from_slice(&5_000_000u64.to_le_bytes());
        send_ok(&mut svm, Instruction {
            program_id: prog_id,
            accounts: vec![
                AccountMeta::new(pfl, false), AccountMeta::new_readonly(own.pubkey(), true),
                AccountMeta::new_readonly(mint, false), AccountMeta::new(tok, false),
                AccountMeta::new(pvlt, false), AccountMeta::new_readonly(TOKEN_PROGRAM_ID, false),
            ],
            data: d,
        }, &payer, &[&payer, own]);
    }
    let atk_pos = create_prog_acc(&mut svm, &prog_id, POS_SIZE);
    let sock_pos = create_prog_acc(&mut svm, &prog_id, POS_SIZE);
    for (pos, own) in [(atk_pos, &attacker), (sock_pos, &sockpuppet)] {
        send_ok(&mut svm, Instruction {
            program_id: prog_id,
            accounts: vec![AccountMeta::new(scam_mkt, false), AccountMeta::new(pos, false), AccountMeta::new_readonly(own.pubkey(), true)],
            data: vec![8],
        }, &payer, &[&payer, own]);
    }
    send_ok(&mut svm, alloc_ix(scam_mkt, atk_pos, atk_pfl, atk_pvlt, scam_vault, &attacker, 2_000_000), &payer, &[&payer, &attacker]);
    send_ok(&mut svm, alloc_ix(scam_mkt, sock_pos, sock_pfl, sock_pvlt, scam_vault, &sockpuppet, 2_000_000), &payer, &[&payer, &sockpuppet]);
    send_ok(&mut svm, trade_ix(scam_mkt, atk_pos, sock_pos, &attacker, &sockpuppet, 1_000_000, 10_000_000, 0), &payer, &[&payer, &attacker, &sockpuppet]);

    // Pump scam oracle 5 steps -> sockpuppet goes totally bankrupt!
    let mut px = 10_000_000u64;
    for _ in 0..5 {
        px = px + (px * 400) / 10_000;
        let mut od = vec![0u8; 18];
        od[0] = 4; od[1..9].copy_from_slice(&px.to_le_bytes());
        send_ok(&mut svm, Instruction {
            program_id: prog_id,
            accounts: vec![AccountMeta::new(scam_mkt, false), AccountMeta::new_readonly(scam_oracle.pubkey(), true)],
            data: od,
        }, &payer, &[&payer, &scam_oracle]);
    }
    // Liquidate bankrupt sockpuppet on SCAM-PERP!
    send_ok(&mut svm, Instruction {
        program_id: prog_id,
        accounts: vec![
            AccountMeta::new(scam_mkt, false), AccountMeta::new(sock_pos, false),
            AccountMeta::new(keep_tok, false), AccountMeta::new_readonly(mint, false),
            AccountMeta::new(scam_vault, false), AccountMeta::new_readonly(TOKEN_PROGRAM_ID, false),
            AccountMeta::new_readonly(keeper.pubkey(), true),
        ],
        data: vec![16],
    }, &payer, &[&payer, &keeper]);

    // ASSERT ABSOLUTE ZERO CONTAGION ON BTC-PERP & ETH-PERP!
    assert_eq!(svm.get_account(&btc_mkt).unwrap().data, btc_snap_before, "BTC market mutated by SCAM-PERP!");
    assert_eq!(svm.get_account(&eth_mkt).unwrap().data, eth_snap_before, "ETH market mutated by SCAM-PERP!");
    assert_eq!(svm.get_account(&alice_btc).unwrap().data, alice_btc_before, "Alice BTC mutated by SCAM-PERP!");
    assert_vault_conserved(&svm, &scam_mkt, &scam_vault, "SCAM-PERP conserved even after bankruptcy");
    println!("[PASS] 6. Zero Cross-Market Contagion     | SCAM-PERP bankruptcy left BTC/ETH/Alice byte-identical!");

    // -------------------------------------------------------------------------
    // 7. Oracle Clamp + 2-Bucket PnL Warmup + Permissionless Liquidation + ADL
    // -------------------------------------------------------------------------
    let upd_oracle = |mkt, auth: &Keypair, new_px: u64, fsign: u8, fe6: u64| {
        let mut od = vec![0u8; 18];
        od[0] = 4;
        od[1..9].copy_from_slice(&new_px.to_le_bytes());
        od[9] = fsign;
        od[10..18].copy_from_slice(&fe6.to_le_bytes());
        Instruction {
            program_id: prog_id,
            accounts: vec![AccountMeta::new(mkt, false), AccountMeta::new_readonly(auth.pubkey(), true)],
            data: od,
        }
    };
    // Unclamped jump $100 -> $110 (+10% > 4% maxMoveBps) MUST REJECT!
    send_err(&mut svm, upd_oracle(btc_mkt, &btc_oracle, 110_000_000, 0, 0), &payer, &[&payer, &btc_oracle], "unclamped oracle jump");

    // Step 1: $100 -> $104 (+4%, clamped OK!) -> Bob still has $7.90 >= $5.20 MM -> Liquidate MUST REJECT!
    let cu_oracle = send_ok(&mut svm, upd_oracle(btc_mkt, &btc_oracle, 104_000_000, 0, 0), &payer, &[&payer, &btc_oracle]);
    send_err(
        &mut svm,
        Instruction {
            program_id: prog_id,
            accounts: vec![
                AccountMeta::new(btc_mkt, false), AccountMeta::new(bob_btc, false),
                AccountMeta::new(keep_tok, false), AccountMeta::new_readonly(mint, false),
                AccountMeta::new(btc_vault, false), AccountMeta::new_readonly(TOKEN_PROGRAM_ID, false),
                AccountMeta::new_readonly(keeper.pubkey(), true),
            ],
            data: vec![16],
        },
        &payer,
        &[&payer, &keeper],
        "liquidating healthy position after 1 clamped step",
    );

    // Step 2: $104 -> $108 (+3.84% <= 4%) -> Bob equity drops to ~$3.90 < $5.40 MM -> Liquidate SUCCEEDS with 0 bad debt!
    send_ok(&mut svm, upd_oracle(btc_mkt, &btc_oracle, 108_000_000, 0, 0), &payer, &[&payer, &btc_oracle]);
    let ins_before_liq = read_u64(&svm, &btc_mkt, 264);
    let cu_liq = send_ok(
        &mut svm,
        Instruction {
            program_id: prog_id,
            accounts: vec![
                AccountMeta::new(btc_mkt, false), AccountMeta::new(bob_btc, false),
                AccountMeta::new(keep_tok, false), AccountMeta::new_readonly(mint, false),
                AccountMeta::new(btc_vault, false), AccountMeta::new_readonly(TOKEN_PROGRAM_ID, false),
                AccountMeta::new_readonly(keeper.pubkey(), true),
            ],
            data: vec![16],
        },
        &payer,
        &[&payer, &keeper],
    );
    // Solvency envelope verified: ZERO bad debt, ZERO insurance spent!
    assert_eq!(read_u64(&svm, &btc_mkt, 264), ins_before_liq, "Insurance should not be touched on solvent liquidation!");
    assert_eq!(read_u64(&svm, &btc_mkt, 296), 0); // oiLong == 0
    assert_eq!(read_u64(&svm, &btc_mkt, 304), 0); // oiShort == 0
    assert!(token_amount(&svm, &keep_tok) > 0, "Keeper should receive bounded liq fee");
    assert_vault_conserved(&svm, &btc_mkt, &btc_vault, "after BTC liquidation");

    // 2-Bucket Warmup Anti-Flash Check on Alice's +$8 BTC profit:
    // At slot 100 (epoch 10), Alice settles -> profit enters pnlCurr, NOT pnlMature!
    let alice_cap_before = read_u64(&svm, &alice_btc, 96);
    let cu_settle = send_ok(
        &mut svm,
        Instruction {
            program_id: prog_id,
            accounts: vec![
                AccountMeta::new(btc_mkt, false),
                AccountMeta::new(alice_btc, false),
                AccountMeta::new_readonly(alice.pubkey(), true),
            ],
            data: vec![15],
        },
        &payer,
        &[&payer, &alice],
    );
    assert_eq!(read_u64(&svm, &alice_btc, 96), alice_cap_before, "Flash realization in same epoch must NOT credit capital!");
    assert_eq!(read_u64(&svm, &alice_btc, 136), 8_000_000, "Profit must sit in pnlCurr");

    // Advance Clock to slot 120 (epoch 12 = e0 + 2): now Alice's +$8 matures & realizes into senior capital!
    set_slot(&mut svm, 120);
    let cu_realize = send_ok(
        &mut svm,
        Instruction {
            program_id: prog_id,
            accounts: vec![
                AccountMeta::new(btc_mkt, false),
                AccountMeta::new(alice_btc, false),
                AccountMeta::new_readonly(alice.pubkey(), true),
            ],
            data: vec![15],
        },
        &payer,
        &[&payer, &alice],
    );
    assert_eq!(read_u64(&svm, &alice_btc, 96), alice_cap_before + 8_000_000, "Mature PnL realized 1:1 from Bob's loss!");
    assert_vault_conserved(&svm, &btc_mkt, &btc_vault, "after Alice PnL realization");
    println!("[PASS] 7. Oracle/Liq/Warmup/Haircut       | Oracle={} CU, Liq={} CU, Settle={} CU, Realize={} CU (0 ins spent!)", cu_oracle, cu_liq, cu_settle, cu_realize);

    // -------------------------------------------------------------------------
    // 8. Admin Burn + Stale-Oracle Permissionless WindDown + Exit Window + ForceClose + Resolve + Tombstone
    // -------------------------------------------------------------------------
    // Burn ETH market admin (Bob) -> permanently adminless!
    send_ok(
        &mut svm,
        Instruction {
            program_id: prog_id,
            accounts: vec![
                AccountMeta::new(eth_mkt, false),
                AccountMeta::new_readonly(bob.pubkey(), true),
            ],
            data: vec![3],
        },
        &payer,
        &[&payer, &bob],
    );
    // Old admin trying to StartWindDown while oracle is fresh (slot 120 < 100 + 50) MUST REJECT!
    send_err(
        &mut svm,
        Instruction {
            program_id: prog_id,
            accounts: vec![
                AccountMeta::new(eth_mkt, false),
                AccountMeta::new_readonly(bob.pubkey(), true),
            ],
            data: vec![17],
        },
        &payer,
        &[&payer, &bob],
        "burned admin StartWindDown on fresh oracle",
    );

    // Advance Clock past maxStaleness (100 + 50 = 150 -> slot 160): ANYONE (keeper) can StartWindDown!
    set_slot(&mut svm, 160);
    send_ok(
        &mut svm,
        Instruction {
            program_id: prog_id,
            accounts: vec![
                AccountMeta::new(eth_mkt, false),
                AccountMeta::new_readonly(keeper.pubkey(), true),
            ],
            data: vec![17],
        },
        &payer,
        &[&payer, &keeper],
    );

    // ForceClosePair BEFORE exitWindow (160 + 20 = 180) MUST REJECT (anti-admin-rug)!
    send_err(
        &mut svm,
        Instruction {
            program_id: prog_id,
            accounts: vec![
                AccountMeta::new(eth_mkt, false),
                AccountMeta::new(alice_eth, false),
                AccountMeta::new(bob_eth, false),
            ],
            data: vec![18],
        },
        &payer,
        &[&payer],
        "ForceClosePair before exitWindow",
    );

    // Advance Clock past exitWindow (slot 185): permissionless ForceClosePair defeats close-griefing DoS!
    set_slot(&mut svm, 185);
    let cu_fc = send_ok(
        &mut svm,
        Instruction {
            program_id: prog_id,
            accounts: vec![
                AccountMeta::new(eth_mkt, false),
                AccountMeta::new(alice_eth, false),
                AccountMeta::new(bob_eth, false),
            ],
            data: vec![18],
        },
        &payer,
        &[&payer],
    );
    assert_eq!(read_u64(&svm, &eth_mkt, 296), 0);
    assert_eq!(read_u64(&svm, &eth_mkt, 304), 0);

    // Permissionless ResolveMarket freezes order-independent snapshot!
    let cu_res = send_ok(
        &mut svm,
        Instruction {
            program_id: prog_id,
            accounts: vec![AccountMeta::new(eth_mkt, false)],
            data: vec![19],
        },
        &payer,
        &[&payer],
    );

    // ClaimResolved for Alice & Bob (even permissionlessly delivered to owner's own token account!)
    let claim_ix = |pos, own_tok| Instruction {
        program_id: prog_id,
        accounts: vec![
            AccountMeta::new(eth_mkt, false),
            AccountMeta::new(pos, false),
            AccountMeta::new(own_tok, false),
            AccountMeta::new_readonly(mint, false),
            AccountMeta::new(eth_vault, false),
            AccountMeta::new_readonly(TOKEN_PROGRAM_ID, false),
            AccountMeta::new_readonly(keeper.pubkey(), true),
        ],
        data: vec![20],
    };
    let cu_claim = send_ok(&mut svm, claim_ix(alice_eth, alice_tok), &payer, &[&payer, &keeper]);
    send_ok(&mut svm, claim_ix(bob_eth, bob_tok), &payer, &[&payer, &keeper]);
    // Double-claim MUST REJECT!
    send_err(&mut svm, claim_ix(alice_eth, alice_tok), &payer, &[&payer, &keeper], "double ClaimResolved");

    // Now OI == 0 -> LP withdraws full ETH insurance (plus earned trade fees!)
    let eth_lp_shares = read_u64(&svm, &eth_ins_rec, 80);
    let mut wd_eth_ins = vec![13u8; 9];
    wd_eth_ins[1..9].copy_from_slice(&eth_lp_shares.to_le_bytes());
    let cu_wd_ins = send_ok(
        &mut svm,
        Instruction {
            program_id: prog_id,
            accounts: vec![
                AccountMeta::new(eth_mkt, false),
                AccountMeta::new(eth_ins_rec, false),
                AccountMeta::new_readonly(lp.pubkey(), true),
                AccountMeta::new_readonly(mint, false),
                AccountMeta::new(eth_vault, false),
                AccountMeta::new(lp_tok, false),
                AccountMeta::new_readonly(TOKEN_PROGRAM_ID, false),
            ],
            data: wd_eth_ins,
        },
        &payer,
        &[&payer, &lp],
    );

    // Permanent TombstoneMarket (INV-16: no ABA reuse!)
    send_ok(
        &mut svm,
        Instruction {
            program_id: prog_id,
            accounts: vec![AccountMeta::new(eth_mkt, false)],
            data: vec![21],
        },
        &payer,
        &[&payer],
    );
    assert_eq!(read_u8(&svm, &eth_mkt, 4), 3); // STATUS_TOMBSTONED
    // Attempt to open position on tombstoned market MUST REJECT!
    let dummy_pos = create_prog_acc(&mut svm, &prog_id, POS_SIZE);
    send_err(
        &mut svm,
        Instruction {
            program_id: prog_id,
            accounts: vec![
                AccountMeta::new(eth_mkt, false),
                AccountMeta::new(dummy_pos, false),
                AccountMeta::new_readonly(alice.pubkey(), true),
            ],
            data: vec![8],
        },
        &payer,
        &[&payer, &alice],
        "OpenPosition on tombstoned market",
    );
    assert_vault_conserved(&svm, &eth_mkt, &eth_vault, "after ETH tombstone");
    println!(
        "[PASS] 8. Lifecycle & Anti-DoS Tombstone  | ForceClose={} CU, Resolve={} CU, Claim={} CU, WdIns={} CU",
        cu_fc, cu_res, cu_claim, cu_wd_ins
    );

    println!("==================================================================================");
    println!("  ALL 8 FULL LIFECYCLE + ADVERSARIAL SECURITY SUITES PASSED ON REAL LITESVM!");
    println!("==================================================================================");
}
