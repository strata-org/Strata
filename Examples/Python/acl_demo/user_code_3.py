import acl

# Bug: assumes any role that can read can also write.
def unsafe_read_then_write(role: str) -> bool:
    client = acl.connect("access_control")
    client.read_resource(role=role, resource_id="docs/guide")
    client.write_resource(role=role, resource_id="docs/guide", content="updated")
    return True