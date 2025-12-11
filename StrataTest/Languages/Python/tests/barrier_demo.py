TPB : int = 8
def dot_product(
    output: LayoutTensor,
    a: LayoutTensor,
    b: LayoutTensor,
    global_i: int,
    local_i: int,
    size: int,
):
    shared : LayoutTensor = LayoutTensor_mk()
    # Compute element-wise multiplication into shared memory
    if global_i < size:
        shared[local_i] = a[global_i] * b[global_i]

    # Synchronize threads within block
    barrier()

    # Parallel reduction in shared memory
    stride: int = TPB // 2
    while stride > 0:
        if local_i < stride:
            shared[local_i] += shared[local_i + stride]

        barrier()
        stride //= 2

    # # Only thread 0 writes the final result
    # if local_i == 0:
    #     output[0] = shared[0]