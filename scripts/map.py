"""Print the selector table of the USDT runtime and its jump destinations as Markdown."""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from disasm import disasm  # noqa: E402
from keccak import keccak256  # noqa: E402

# Candidate signatures, checked against the selectors found in the bytecode.
SIGS = ["name()", "deprecate(address)", "approve(address,uint256)", "deprecated()",
        "addBlackList(address)", "totalSupply()", "transferFrom(address,address,uint256)",
        "upgradedAddress()", "balances(address)", "decimals()", "maximumFee()",
        "_totalSupply()", "unpause()", "getBlackListStatus(address)",
        "allowed(address,address)", "paused()", "balanceOf(address)", "pause()",
        "getOwner()", "owner()", "symbol()", "transfer(address,uint256)",
        "setParams(uint256,uint256)", "issue(uint256)", "redeem(uint256)",
        "allowance(address,address)", "basisPointsRate()", "isBlackListed(address)",
        "removeBlackList(address)", "MAX_UINT()", "transferOwnership(address)",
        "destroyBlackFunds(address)"]
NAMES = {keccak256(s.encode())[:4].hex(): s for s in SIGS}

code = bytes.fromhex(open(sys.argv[1]).read().strip())
ins = list(disasm(code))
print("| entry pc | selector | signature | destination |")
print("|---|---|---|---|")
for i in range(len(ins) - 4):
    a, b, c, d, e = ins[i:i + 5]
    if (a[2], b[2], c[2], d[2], e[2]) == ("DUP1", "PUSH4", "EQ", "PUSH2", "JUMPI"):
        print(f"| {a[0]} | 0x{b[3]} | {NAMES.get(b[3], '?')} | {int(d[3], 16)} (0x{d[3]}) |")
dests = [pc for pc, op, name, _ in ins if name == "JUMPDEST"]
print()
print(f"Instructions: {len(ins)}; JUMPDESTs at an opcode boundary: {len(dests)}.")
