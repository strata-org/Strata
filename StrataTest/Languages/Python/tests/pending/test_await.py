import asyncio

async def get_val():
    return 42

async def main():
    r = await get_val()
    assert r == 42, "await"

asyncio.run(main())
