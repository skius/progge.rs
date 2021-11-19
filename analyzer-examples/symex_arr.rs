fn analyze(i: int, j: int, x: int, y: int) {
    let arr = [1, 2, 3];
    assume!(i != j);
    arr[x] = i;
    arr[y] = j;
    if arr[x] == arr[y] {
        // Demonstrates something similar to aliasing
        testcase!;
    }
    arr_modifier(arr);
    if arr[x] == arr[y] {
        // Note the different models, this is because arrays are by-reference
        testcase!;
    }

    return;
}

fn arr_modifier(arr: [int]) {
    arr[2] = (arr[0] + arr[1])/2;
    return;
}