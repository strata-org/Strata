# Test: **kwargs patterns typical of boto3/service SDK usage

import boto3

def put_item(client, bucket: str, key: str, data: str):
    """Direct keyword args - the common boto3 pattern."""
    client.put_item(Bucket=bucket, Key=key, Data=data)

def put_item_from_dict(client, params: dict):
    """Unpacking a dict as kwargs."""
    client.put_item(**params)

def build_and_call(client, bucket: str, key: str):
    """Build kwargs dict incrementally then unpack."""
    kwargs = {"Bucket": bucket, "Key": key}
    kwargs["Data"] = "payload"
    client.put_item(**kwargs)

# Module-level: typical boto3 usage
iam = boto3.client("iam")
iam.get_role(RoleName="my-role")
