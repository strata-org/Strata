import asyncio

async def get_val():
    return 42

def test():
    r = asyncio.run(get_val())
    assert r == 42, "async def"
test()
