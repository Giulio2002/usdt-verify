# Source of `usdt.runtime.hex`

- Contract: TetherToken (USDT), 0xdAC17F958D2ee523a2206206994597C13D831ec7, Ethereum mainnet.
- Fetched on 2026-11-07 with one JSON-RPC `eth_getCode` call at block tag `latest`.
- Endpoint: https://ethereum-rpc.publicnode.com (generic User-Agent, no other data sent).
- `eth_blockNumber` on the same endpoint just before: 0x1924448 = 26362952.
- Size: 11075 bytes.
- keccak256: 0xb44fb4e949d0f78f87f79ee46428f23a2a5713ce6fc6e0beb3dda78c2ac1ea55
  (from `scripts/keccak.py`, pure Python; the Lean test `UsdtVerify/Test/Hash.lean`
  recomputes it with EthLib's Keccak-256 and checks the bytes against this file).
