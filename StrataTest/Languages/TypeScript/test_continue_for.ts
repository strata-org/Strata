let j = 0;

for (let i = 1; i < 10; i = i + 1) {
    if (i % 2 === 0) {
        continue;
    }
    j = j + 1;
}