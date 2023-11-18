# Bomblab

## 실습

### bomblab

** 예상 코드 및 정답

- 2번

```cpp
/*
<idea>

1. A ( 0보다 크거나 같으면 됨 )
2. A + 1
3. A + 1 + 2
4. A + 1 + 2 + 3
5. A + 1 + 2 + 3 + 4
6. A + 1 + 2 + 3 + 4 + 5
*/

// 정답 코드
int A;
cin << A;
for (int i = 0; i <= 5; ++i) {
	A += i;
	cout << A << " ";
}
```

---

- 3번

입력 포맷 : %d %c %d

첫 번째 입력 값이 7보다 크면 안됨. (음수도 안됨. 부호가 없는 비교임)

첫 번째가 인덱스이고, 인덱스에 맞는 두 번째 값과 세 번째 값이 있음.

<정답>

0 u 312

1 p 428

2 p 604

3 o 324

4 z 944

5 y 55

6 t 418

7 j 896

---

- 4번

입력 포맷 : %d %d

첫 번째 입력 값이 14보다 작거나 같아야 함. (음수도 안됨. 부호가 없는 비교임)

두 번째 입력 값은 15가 되어야 함.

```cpp
// 정답 코드
int test(int a, int b = 0, int c = 14) {
    int tmp = c - b;
    tmp += tmp >> 31;
    tmp >>= 1;
    tmp += b;

    if (a >= tmp) {
        if (a <= tmp) return tmp;
        else {
            return tmp + test(a, tmp + 1, c);
        }
    } else {
        return tmp + test(a, b, tmp - 1);
    }
}

int main() {
    cin.tie(0);
    ios_base::sync_with_stdio(false);

    for (int i = 0; i <= 14; ++i) {
        cout << test(i) << " ";
    }

    return 0;
}

// 11 11 13 10 19 15 21 7 35 27 37 18 43 31 45
// 인덱스가 5일 때, 정답 15가 나옴.
```

<정답>

5 15

---

- 5번

입력 값은 문자열, 길이는 6이어야 함.

각 문자를 16진수로 변환 했을 때 하위 1바이트의 index에 해당하는 값으로 첫번 째부터 채워나감.

예상되는 코드는 다음과 같음.

```cpp
char A[7];
char B[7];

char[] words = "maduiersnfotvbylSo you think you can stop the bomb with ctrl-c, do you?";

cin << A;
if (string_length(A) != 6) exit(0);

for (int i = 0; i <= 5; ++i) {
	B[i] = words[(A & 0xf)];
}

if (strings_not_equal(A, B)) exit(0);

// 정답 : oilers
// index : 10 4 15 5 6 7
// to hex : a 4 f 5 6 7
// 가능한 정답 :
// (*, :, J, Z, j, z)
// ($, 4, D, T, d, t)
// (/, ?, O, _, o)
// (%, 5, E, U, e, u)
// (&, 6, F, V, f, v)
// (', 7, G, W, g, w)
```

---

- 6번

첫 번째 값이 6보다 작거나 같고 0보다 커야 함.

두 번째 값은 첫 번째 값이랑 같지 않아야 함.

```cpp
#include <iostream>
using namespace std;

struct Node {
	int value;
	int index;
	struct Node* next;
};

int A[6];
Node* B[6];
Node* C[6];

int main() {
    // cin.tie(0);
    // ios_base::sync_with_stdio(false);

    for (int i = 0; i < 6; ++i) C[i] = (Node*)malloc(sizeof(Node));
    *C[5] = {0x36, 6, 0};
    *C[4] = {0xf8, 5, C[6]};
    *C[3] = {0x1d2, 4, C[5]};
    *C[2] = {0x166, 3, C[4]};
    *C[1] = {0x247, 2, C[3]};
    *C[0] = {0x20f, 1, C[2]};

    for (int i = 0; i < 6; ++i) cin >> A[i]; // 1 <= input <= 6

    for (int i = 0; i < 6; ++i) {
        for (int j = i + 1; j < 6; ++j) {
            if (A[i] == A[j]) {
                cout << "bomb!!\n";
                exit(0); // bomb!!
            }
        }
    }

    for (int i = 0; i < 6; ++i) {
        A[i] = 6 - A[i];
    }

    for (int i = 0; i < 6; ++i) {
        B[i] = C[A[i]];
    }

    for (int i = 0; i < 5; ++i) {
        B[i]->next = B[i + 1];
    }
    B[5]->next = 0;

    for (int i = 0; i < 5; ++i) {
        if (B[i]->value < B[i]->next->value) {
            cout << "bomb!!\n";
            exit(0); // bomb!!
        }
    }

    cout << "success\n";

    return 0;
}

// 정답 : 5 6 3 4 2 1
```
