import acl

# Fixed: guards read and write.
def safe_read_then_write(role: str) -> bool:
    client = acl.connect("access_control")
    if role == "admin" or role == "editor":
        client.read_resource(role=role, resource_id="docs/guide")
        client.write_resource(role=role, resource_id="docs/guide", content="updated")
    return True
