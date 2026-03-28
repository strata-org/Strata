# Negative test: async function → stub with correct signature, no body
# Expected: warning about unsupported async, stub generated

import asyncio

async def fetch_data(url: str) -> str:
    result = await asyncio.get(url)
    return result

def sync_helper(x: int) -> int:
    return x + 1
