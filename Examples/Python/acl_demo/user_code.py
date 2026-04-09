import acl

# --- Concrete: specific usage, everything passes ---

def admin_workflow() -> bool:
    client = acl.connect("access_control")
    client.read_resource(role="admin", resource_id="secrets/key")
    client.write_resource(role="admin", resource_id="config/settings", content="timeout=30")
    client.delete_resource(role="admin", resource_id="tmp/cache")
    return True

# --- Symbolic: does the logic hold for ANY role? ---

# The solver uses the if-guard to prove delete is safe,
# but flags read_resource — an arbitrary role might not be valid.
def conditional_delete(role: str) -> bool:
    client = acl.connect("access_control")
    client.read_resource(role=role, resource_id="data/report")
    if role == "admin":
        client.delete_resource(role=role, resource_id="tmp/cache")
    return True

# Bug: assumes any role that can read can also write.
def unsafe_read_then_write(role: str) -> bool:
    client = acl.connect("access_control")
    client.read_resource(role=role, resource_id="docs/guide")
    client.write_resource(role=role, resource_id="docs/guide", content="updated")
    return True

# Fixed: guards write behind an editor/admin check.
def safe_read_then_write(role: str) -> bool:
    client = acl.connect("access_control")
    client.read_resource(role=role, resource_id="docs/guide")
    if role == "admin" or role == "editor":
        client.write_resource(role=role, resource_id="docs/guide", content="updated")
    return True
