# Negative test: mix of supported and unsupported features
# Expected: SSA generated for supported parts, warnings for unsupported
# The supported function should have full SSA, the async one gets a stub

import asyncio

def sync_add(a: int, b: int) -> int:
    return a + b

async def async_fetch(url: str) -> str:
    return await asyncio.get(url)

items = [1, 2, 3]
doubled = [x * 2 for x in items]  # unsupported expr
result = sync_add(1, 2)           # fully supported
