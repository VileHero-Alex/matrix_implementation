#include <algorithm>
#include <cassert>
#include <cmath>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>

long long binpow(long long a, long long n);

class BigInteger {
  private:
    static const long long base_ = 9;
    int sgn = 1;
    size_t sz_ = 0;
    static constexpr long long maxDig_ = 1e9;
    std::vector<long long> digits_;

    void swap(BigInteger& x);

    void sum(const BigInteger& x);
    void diff(const BigInteger& x);

    void removeRedundant();

    void Division(int is_quotient, const BigInteger& a);

  public:
    BigInteger(long long a);
    BigInteger(const std::string& str);
    BigInteger();

    BigInteger& operator+=(const BigInteger& a);
    BigInteger& operator-=(const BigInteger& a);
    BigInteger& operator*=(const BigInteger& a);
    BigInteger& operator/=(const BigInteger& a);
    BigInteger& operator%=(const BigInteger& a);

    void change_sign(int val_);
    size_t size() const;
    int sign() const;

    void clear();

    long long operator[](size_t index) const;

    std::string toString() const;

    BigInteger operator-() const;

    BigInteger& operator++();
    BigInteger operator++(int);
    BigInteger& operator--();
    BigInteger operator--(int);

    explicit operator bool() const;

    friend void swap_bigInts(BigInteger& x, BigInteger& y);
};

std::istream& operator>>(std::istream& in, BigInteger& x);
std::ostream& operator<<(std::ostream& out, const BigInteger& x);

BigInteger gcd(BigInteger x, BigInteger y);

BigInteger operator+(const BigInteger& a, const BigInteger& b);
BigInteger operator-(const BigInteger& a, const BigInteger& b);
BigInteger operator*(const BigInteger& a, const BigInteger& b);
BigInteger operator/(const BigInteger& a, const BigInteger& b);
BigInteger operator%(const BigInteger& a, const BigInteger& b);

bool operator==(const BigInteger& a, const BigInteger& b);
bool operator<(const BigInteger& a, const BigInteger& b);
bool operator!=(const BigInteger& a, const BigInteger& b);
bool operator>(const BigInteger& a, const BigInteger& b);
bool operator<=(const BigInteger& a, const BigInteger& b);
bool operator>=(const BigInteger& a, const BigInteger& b);

BigInteger operator""_bi(unsigned long long x);
BigInteger operator""_bi(const char* x, size_t /*unused*/);

class Rational {
  private:
    int sgn = 1;
    BigInteger a_ = 0, b_ = 1;

    void swap_rational(Rational& x);
    void cutTheFraction(Rational& nw);
    static void oppositeForWholeFractionIfNeeded(Rational& nw, BigInteger& x);
    static void oppositeForNumeratorOrDenomimatorIfNeeded(BigInteger& x);

  public:
    Rational(const BigInteger& x);
    Rational(long long x);
    Rational(int x);
    Rational();

    Rational operator-() const;

    const BigInteger& getNumerator() const;
    const BigInteger& getDenominator() const;

    std::string toString() const;
    static std::string asDecimalToString(const BigInteger& beforeDot,
                                         const BigInteger& afterDot,
                                         size_t precision = 0);

    int sign() const;

    Rational& operator+=(const Rational& x);
    Rational& operator-=(const Rational& x);
    Rational& operator*=(const Rational& x);
    Rational& operator/=(const Rational& x);

    std::string asDecimal(size_t precision = 0) const;

    explicit operator double() const;

    friend std::istream& operator>>(std::istream& is, Rational& q);

    friend std::ostream& operator<<(std::ostream& os, const Rational& q);
};

Rational abs(const Rational& a);
Rational operator+(const Rational& a, const Rational& b);
Rational operator-(const Rational& a, const Rational& b);
Rational operator*(const Rational& a, const Rational& b);
Rational operator/(const Rational& a, const Rational& b);

bool operator==(const Rational& a, const Rational& b);
bool operator<(const Rational& a, const Rational& b);
bool operator!=(const Rational& a, const Rational& b);
bool operator>(const Rational& a, const Rational& b);
bool operator<=(const Rational& a, const Rational& b);
bool operator>=(const Rational& a, const Rational& b);

template <int N, int K, bool fl>
struct IsPrimeHelper {
    static const bool value =
        (N % K == 0) ? false : IsPrimeHelper<N, K + 1, K * K <= N>::value;
};

template <int N, int K>
struct IsPrimeHelper<N, K, false> {
    static const bool value = true;
};

template <int K, bool flag>
struct IsPrimeHelper<2, K, flag> {
    static const bool value = true;
};

template <int K, bool flag>
struct IsPrimeHelper<1, K, flag> {
    static const bool value = false;
};

template <int N>
struct IsPrime {
    static const bool value = IsPrimeHelper<N, 2, true>::value;
};

template <size_t N>
class Residue {
  private:
    int val_;

    static void makeValCorrect(Residue<N>& a) {
        if (a.val_ >= 0) {
            a.val_ %= N;
            return;
        }
        int c = -((a.val_ >= 0 ? a.val_ : -a.val_) / N) - 1;
        a.val_ = (a.val_ - c * N) % N;
    }

  public:
    int getVal(Residue<N>& a) {
        return a.val_;
    }

    Residue<N>(){};

    Residue<N>(int x) : val_(x) {
        makeValCorrect(*this);
    }

    Residue<N>& operator+=(const Residue<N>& b) {
        val_ += b.val_;
        val_ %= N;
        return *this;
    }

    Residue<N>& operator-=(const Residue<N>& b) {
        val_ -= b.val_;
        if (val_ < 0) {
            val_ += N;
        }
        return *this;
    }

    Residue<N>& operator*=(const Residue<N>& b) {
        val_ *= b.val_;
        val_ %= N;
        return *this;
    }

    Residue<N>& operator/=(const Residue<N>& b) {
        static_assert(
            IsPrime<N>::value,
            "Not allowed to use operations / and /=, N is not prime.");
        size_t x = b.val_;
        long long MOD = N;
        size_t n = N - 2;
        size_t res = 1;
        while (n != 0) {
            if ((n & 1) != 0u) {
                res = ((res % MOD) * (x % MOD)) % MOD;
            }
            x = ((x % MOD) * (x % MOD)) % MOD;
            n >>= 1;
        }
        val_ = res * val_ % MOD;
        return *this;
    }

    operator int() const {
        return val_;
    }

    int abs(Residue<N>& x) {
        return x.val_;
    }

    bool operator==(const Residue<N>& b) const {
        return val_ == b.val_;
    }

    bool operator!=(const Residue<N>& b) const {
        return !(val_ == b.val_);
    }

    friend std::istream& operator>>(std::istream& is, Residue<N>& a) {
        int x;
        is >> x;
        a.val_ = x;
        makeValCorrect(a);
        return is;
    }

    friend std::ostream& operator<<(std::ostream& out, const Residue<N>& a) {
        out << a.val_;
        return out;
    }
};

template <size_t N>
Residue<N> operator+(const Residue<N>& a, const Residue<N>& b) {
    Residue<N> res = a;
    res += b;
    return res;
}

template <size_t N>
Residue<N> operator-(const Residue<N>& a, const Residue<N>& b) {
    Residue<N> res = a;
    res -= b;
    return res;
}

template <size_t N>
Residue<N> operator*(const Residue<N>& a, const Residue<N>& b) {
    Residue<N> res = a;
    res *= b;
    return res;
}

template <size_t N>
Residue<N> operator/(const Residue<N>& a, const Residue<N>& b) {
    Residue<N> res = a;
    res /= b;
    return res;
}

template <size_t N>
bool operator==(const Residue<N>& a, const Residue<N>& b) {
    return a.getVal() == b.getVal();
}

template <size_t N>
bool operator<(const Residue<N>& a, const Residue<N>& b) {
    return a.getVal() < b.getVal();
}

template <size_t N>
bool operator>(const Residue<N>& a, const Residue<N>& b) {
    return b < a;
}

template <size_t N>
bool operator<=(const Residue<N>& a, const Residue<N>& b) {
    return !(a > b);
}

template <size_t N>
bool operator>=(const Residue<N>& a, const Residue<N>& b) {
    return !(a < b);
}

template <size_t N, size_t M, typename Field = Rational>
class Matrix {
  private:
    std::vector<std::vector<Field>> data =
        std::vector<std::vector<Field>>(N, std::vector<Field>(M));
    Field constZero_ = 0;
    Field constOne_ = 1;

  public:
    Matrix<N, M, Field>() {
        for (size_t i = 0; i < N; ++i) {
            for (size_t j = 0; j < M; ++j) {
                data[i][j] = 0;
            }
        }
    }

    Matrix<N, M, Field>(std::initializer_list<std::initializer_list<Field>> a) {
        size_t i = 0;
        for (auto row : a) {
            size_t j = 0;
            for (auto elem : row) {
                data[i][j] = elem;
                ++j;
            }
            ++i;
        }
    }

    bool operator!=(const Matrix<N, M, Field>& other) {
        return !(*this == other);
    }

    std::vector<Field>& operator[](size_t i) {
        return data[i];
    }

    std::vector<Field> operator[](size_t i) const {
        return data[i];
    }

    friend std::istream& operator>>(std::istream& is,
                                    Matrix<N, M, Field>& cur) {
        std::ios_base::sync_with_stdio(false);
        std::cin.tie(nullptr);

        Field x;
        for (size_t i = 0; i < N; i++) {
            for (size_t j = 0; j < M; j++) {
                is >> x;
                cur[i][j] = x;
            }
        }
        return is;
    }

    friend std::ostream& operator<<(std::ostream& os,
                                    const Matrix<N, M, Field>& cur) {
        for (size_t i = 0; i < N; i++) {
            for (size_t j = 0; j < M; j++) {
                os << cur[i][j] << " ";
            }
            os << "\n";
        }
        return os;
    }

    Matrix<N, M, Field>& operator+=(Matrix<N, M, Field> other) {
        for (size_t i = 0; i < N; ++i) {
            for (size_t j = 0; j < M; ++j) {
                data[i][j] += other[i][j];
            }
        }
        return *this;
    }

    Matrix<N, M, Field>& operator-=(Matrix<N, M, Field> other) {
        for (size_t i = 0; i < N; ++i) {
            for (size_t j = 0; j < M; ++j) {
                data[i][j] -= other[i][j];
            }
        }
        return *this;
    }

    Matrix<N, M, Field> operator+(const Matrix<N, M, Field>& other) const {
        Matrix<N, M, Field> res = *this;
        res += other;
        return res;
    }

    Matrix<N, M, Field> operator-(const Matrix<N, M, Field>& other) const {
        Matrix<N, M, Field> res = *this;
        res -= other;
        return res;
    }

    Matrix<N, M, Field>& operator*=(const Field& b) {
        for (size_t i = 0; i < N; ++i) {
            for (size_t j = 0; j < M; ++j) {
                data[i][j] *= b;
            }
        }
        return *this;
    }

    Matrix<N, M, Field>& operator*(const Field& b) const {
        Matrix<N, M, Field> res = *this;
        res *= b;
        return res;
    }

    template <size_t K>
    Matrix<N, K, Field> operator*(const Matrix<M, K, Field>& other) const {
        Matrix<N, K, Field> res;
        for (size_t i = 0; i < N; ++i) {
            for (size_t k = 0; k < M; ++k) {
                for (size_t j = 0; j < K; ++j) {
                    res[i][j] += data[i][k] * other[k][j];
                }
            }
        }
        return res;
    }

    Matrix<N, N, Field>& operator*=(const Matrix<N, N, Field>& other) {
        *this = *this * other;
        return *this;
    }

    Field trace() const {
        static_assert(N == M, "Not allowed to find trace, N is not equal M");
        Field res = 0;
        for (size_t i = 0; i < N; i++) {
            res += data[i][i];
        }
        return res;
    }

    std::vector<Field> getRow(size_t i) const {
        return data[i];
    }

    std::vector<Field> getColumn(size_t i) const {
        std::vector<Field> res(N);
        for (size_t k = 0; k < N; ++k) {
            res[k] = data[k][i];
        }
        return res;
    }

    Matrix<M, N, Field> transposed() const {
        Matrix<M, N, Field> res;
        for (size_t i = 0; i < N; ++i) {
            for (size_t j = 0; j < M; ++j) {
                res[j][i] = data[i][j];
            }
        }
        return res;
    }

    Field det() const {
        static_assert(N == M,
                      "Not allowed to find determinant, N is not equal M");
        Field det = 1;
        Matrix<N, N, Field> matrix = *this;
        for (size_t i = 0; i < N; ++i) {
            Field pivotElement = matrix[i][i];
            size_t pivotRow = i;
            for (size_t row = i + 1; row < N; ++row) {
                if (abs(matrix[row][i]) > abs(pivotElement)) {
                    pivotElement = matrix[row][i];
                    pivotRow = row;
                }
            }
            if (pivotElement == constZero_) {
                return constZero_;
            }
            if (pivotRow != i) {
                matrix[i].swap(matrix[pivotRow]);
                det *= -constOne_;
            }
            det *= pivotElement;
            for (size_t row = i + 1; row < N; ++row) {
                for (size_t col = i + 1; col < N; ++col) {
                    matrix[row][col] -=
                        ((matrix[row][i] * matrix[i][col]) / pivotElement);
                }
            }
        }
        return det;
    }

    size_t rank() const {
        Matrix<N, M, Field> matrix = *this;
        size_t rg = 0;
        std::vector<bool> row_selected(N, false);
        for (size_t i = 0; i < M; ++i) {
            size_t j;
            for (j = 0; j < N; ++j) {
                if ((!row_selected[j]) && (matrix[j][i] != constZero_)) {
                    break;
                }
            }
            if (j != N) {
                ++rg;
                row_selected[j] = true;
                for (size_t p = i + 1; p < M; ++p) {
                    matrix[j][p] /= matrix[j][i];
                }
                for (size_t k = 0; k < N; ++k) {
                    if ((k != j) && (matrix[k][i] != constZero_)) {
                        for (size_t p = i + 1; p < M; ++p) {
                            matrix[k][p] -= matrix[j][p] * matrix[k][i];
                        }
                    }
                }
            }
        }
        return rg;
    }

    void invert() {
        static_assert(N == M, "Not allowed to invert matrix, N != M");
        Matrix<N, M, Field> inv;
        for (size_t i = 0; i < N; ++i) {
            inv[i][i] = Field(1);
        }
        Matrix<N, M, Field> gauss = *this;
        size_t pos = 0;
        for (size_t col = 0; col < M; ++col) {
            bool sw = false;
            for (size_t row = pos; row < M; ++row) {
                if (gauss[row][col] != Field(0)) {
                    std::swap(gauss[pos], gauss[row]);
                    std::swap(inv[pos], inv[row]);
                    sw = true;
                    break;
                }
            }
            if (!sw) {
                continue;
            }
            Field lead = gauss[pos][col];
            for (size_t row = pos + 1; row < M; ++row) {
                Field cf = gauss[row][col] / lead;
                if (cf == Field(0)) {
                    continue;
                }
                for (size_t i = 0; i < M; ++i) {
                    gauss[row][i] -= cf * gauss[pos][i];
                    inv[row][i] -= cf * inv[pos][i];
                }
            }
            ++pos;
        }
        for (size_t i = M; i-- > 0;) {
            Field lead = gauss[i][i];
            for (size_t row = 0; row < i; ++row) {
                Field cf = gauss[row][i] / lead;
                if (cf == Field(0)) {
                    continue;
                }
                for (size_t j = 0; j < M; ++j) {
                    gauss[row][j] -= cf * gauss[i][j];
                    inv[row][j] -= cf * inv[i][j];
                }
            }
            for (size_t j = 0; j < M; ++j) {
                inv[i][j] /= gauss[i][i];
            }
        }
        *this = inv;
    }

    Matrix<N, N, Field> inverted() const {
        Matrix<N, N, Field> A = *this;
        A.invert();
        return A;
    }
};

template <size_t N, size_t M, typename Field = Rational>
bool operator==(const Matrix<N, M, Field>& A, const Matrix<N, M, Field>& B) {
    for (size_t i = 0; i < N; ++i) {
        for (size_t j = 0; j < M; ++j) {
            if (A[i][j] != B[i][j]) {
                return false;
            }
        }
    }
    return true;
}

template <size_t N, size_t M, typename Field = Rational>
Matrix<N, M, Field> operator*(const Field& val, const Matrix<N, M, Field>& A) {
    Matrix<N, M, Field> ans = A;
    ans *= val;
    return ans;
}

template <size_t N, typename Field = Rational>
using SquareMatrix = Matrix<N, N, Field>;

long long binpow(long long a, long long n) {
    if (n == 0) {
        return 1;
    }
    if (n % 2 == 1) {
        return a * binpow(a, n - 1);
    } else {
        long long b = binpow(a, n / 2);
        return b * b;
    }
}

void BigInteger::swap(BigInteger& x) {
    std::swap(sz_, x.sz_);
    std::swap(sgn, x.sgn);

    std::swap(digits_, x.digits_);
}

BigInteger::BigInteger() : sz_(1), digits_(1) {}

BigInteger::BigInteger(const std::string& str) {
    if (str[0] == '-') {
        sgn *= -1;
    }
    long long cnt = 0;
    long long now = 0;
    for (size_t i = str.size(); i > 0; --i) {
        if (str[i - 1] == '-') {
            break;
        }
        if (cnt == base_) {
            cnt = 0;
            digits_.push_back(now);
            ++sz_;
            now = 0;
        }
        ++cnt;
        now += (str[i - 1] - '0') * binpow(10, cnt - 1);
    }
    if (cnt != 0) {
        digits_.push_back(now);
        ++sz_;
    }
}

BigInteger::BigInteger(long long a) {
    if (a < 0) {
        sgn = -sgn;
        a *= -1;
    }
    while (a > 0) {
        digits_.push_back(a % maxDig_);
        ++sz_;
        a /= maxDig_;
    }
    if (digits_.empty()) {
        ++sz_;
        digits_.push_back(0);
    }
}

BigInteger operator""_bi(unsigned long long x) {
    BigInteger temp(x);
    return temp;
}

BigInteger operator""_bi(const char* x, size_t /*unused*/) {
    BigInteger temp(x);
    return temp;
}

std::string BigInteger::toString() const {
    if (sz_ == 1 && digits_[0] == 0) {
        return "0";
    }
    std::string res;
    if (sgn == -1) {
        res += '-';
    }
    for (int i = sz_ - 1; i >= 0; --i) {
        std::string tmp = std::to_string(digits_[i]);
        reverse(tmp.begin(), tmp.end());
        if (i != static_cast<int>(digits_.size()) - 1) {
            while (static_cast<int>(tmp.size()) < base_) {
                tmp += '0';
            }
        }
        reverse(tmp.begin(), tmp.end());
        res += tmp;
    }
    return res;
}

size_t BigInteger::size() const {
    return sz_;
}

int BigInteger::sign() const {
    return sgn;
}

void BigInteger::clear() {
    digits_.clear();
    digits_.push_back(0);
    sz_ = 1;
    sgn = 1;
}

long long BigInteger::operator[](size_t index) const {
    return digits_[index];
}

BigInteger BigInteger::operator-() const {
    if (sz_ == 1 && digits_[0] == 0) {
        return *this;
    }
    BigInteger copy = *this;
    copy.sgn *= -1;
    return copy;
}

void BigInteger::change_sign(int val) {
    sgn = val;
}

void BigInteger::removeRedundant() {
    while (digits_.size() > 1 && digits_.back() == 0) {
        digits_.pop_back();
        --sz_;
    }
}

void BigInteger::sum(const BigInteger& x) {
    long long rem = 0;
    size_t mx = std::max(x.size(), sz_);
    size_t i;
    for (i = 0; i < mx; ++i) {
        long long a = 0, b = 0, c = 0;
        if (i < sz_) {
            a = digits_[i];
        }
        if (i < x.size()) {
            b = x.digits_[i];
        }
        c = a + b + rem;
        if (i == sz_) {
            ++sz_;
            digits_.push_back(c % maxDig_);
        } else {
            digits_[i] = c % maxDig_;
        }
        rem = c / maxDig_;
    }
    while (rem > 0) {
        if (i == sz_) {
            ++sz_;
            digits_.push_back(rem % maxDig_);
        }
        rem = rem / maxDig_;
    }
    removeRedundant();
}

void BigInteger::diff(const BigInteger& x) {
    while (digits_.size() < x.digits_.size()) {
        digits_.push_back(0);
    }
    for (size_t i = 0; i < x.digits_.size(); ++i) {
        digits_[i] -= x.digits_[i];
    }
    int idx_pos = -1, idx_neg = -1;
    for (size_t i = 0; i < digits_.size(); ++i) {
        if (digits_[i] < 0) {
            idx_neg = i;
        }
        if (digits_[i] > 0) {
            idx_pos = i;
        }
    }
    if (idx_pos < idx_neg) {
        sgn *= -1;
        for (size_t i = 0; i < digits_.size(); ++i) {
            digits_[i] *= -1;
        }
    }
    bool need_help = false;
    for (size_t i = 0; i < digits_.size(); ++i) {
        if (need_help && digits_[i] <= 0) {
            digits_[i] += maxDig_ - 1;
        } else if (need_help) {
            --digits_[i];
            need_help = false;
        } else if (digits_[i] < 0) {
            digits_[i] += maxDig_;
            need_help = true;
        }
    }
    removeRedundant();
}

BigInteger& BigInteger::operator-=(const BigInteger& a) {
    if (sgn != a.sign()) {
        sgn *= -1;
        (*this) += a;
        sgn *= -1;
        return *this;
    }
    diff(a);
    if (sz_ == 1 && digits_[0] == 0) {
        sgn = 1;
    }
    return *this;
}

BigInteger& BigInteger::operator+=(const BigInteger& a) {
    if (sgn != a.sign()) {
        sgn *= -1;
        *this -= a;
        sgn *= -1;
        return *this;
    }
    sum(a);
    if (sz_ == 1 && digits_[0] == 0) {
        sgn = 1;
    }
    return *this;
}

BigInteger operator+(const BigInteger& a, const BigInteger& b) {
    BigInteger temp = a;
    temp += b;
    return temp;
}

BigInteger operator-(const BigInteger& a, const BigInteger& b) {
    BigInteger temp = a;
    temp -= b;
    return temp;
}

BigInteger& BigInteger::operator++() {
    *this += 1;
    return *this;
}

BigInteger BigInteger::operator++(int) {
    BigInteger copy = *this;
    ++(*this);
    return copy;
}

BigInteger& BigInteger::operator--() {
    *this -= 1;
    return *this;
}

BigInteger BigInteger::operator--(int) {
    BigInteger copy = *this;
    --copy;
    return copy;
}

BigInteger& BigInteger::operator*=(const BigInteger& a) {
    bool neg = false;
    if (sgn != a.sign()) {
        neg = true;
    }
    BigInteger temp(0);
    for (size_t i = 0; i < a.size(); ++i) {
        long long rememb = 0;
        long long cur = a.digits_[i];
        for (size_t j = 0; j < sz_; ++j) {
            long long b = digits_[j];
            long long c = b * cur + rememb;
            while (temp.size() <= i + j) {
                temp.digits_.push_back(0);
                ++temp.sz_;
            }
            temp.digits_[i + j] += c % maxDig_;
            rememb = c / maxDig_;
        }
        size_t post_j = sz_;
        while (rememb > 0) {
            while (temp.size() <= i + post_j) {
                temp.digits_.push_back(0);
                ++temp.sz_;
            }
            temp.digits_[i + post_j] += rememb % maxDig_;
            ++post_j;
            rememb = rememb / maxDig_;
        }
        temp += 0_bi;
    }
    swap(temp);
    if (neg) {
        sgn = -1;
    }
    if (sz_ == 1 && digits_[0] == 0) {
        sgn = 1;
    }
    return *this;
}

void BigInteger::Division(int is_quotient, const BigInteger& a) {
    bool neg = false;
    if (sgn != a.sign()) {
        neg = true;
    }
    bool fl = true;
    if (a.sign() == -1) {
        fl = false;
    }
    BigInteger res(0);
    BigInteger rememb(0);
    for (size_t i = sz_; i > 0; --i) {
        BigInteger cur = digits_[i - 1] + rememb * maxDig_;
        long long l = 0, r = maxDig_;
        while (l + 1 < r) {
            long long md = (l + r) >> 1LL;
            if (a * md <= cur) {
                l = md;
            } else {
                r = md;
            }
        }
        if (fl) {
            cur -= (a * l);
        } else {
            cur += (a * l);
        }
        if (sz_ - i >= res.size()) {
            res.digits_.push_back(0);
            ++res.sz_;
        }
        res.digits_[sz_ - i] = l;
        rememb = cur;
    }
    if (is_quotient != 0) {
        std::reverse(res.digits_.begin(), res.digits_.end());
        swap(res);
    } else {
        swap(rememb);
    }
    removeRedundant();
    if (neg) {
        sgn = -1;
    }
    if (sz_ == 1 && digits_[0] == 0) {
        sgn = 1;
    }
}

BigInteger& BigInteger::operator/=(const BigInteger& a) {
    if (a.size() == 1 && a.digits_[0] == 0) {
        throw std::runtime_error("Division by 0");
    }
    Division(1, a);
    return *this;
}

BigInteger& BigInteger::operator%=(const BigInteger& a) {
    if (a.size() == 1 && a.digits_[0] == 0) {
        throw std::runtime_error("Division by 0");
    }
    Division(0, a);
    return *this;
}

BigInteger operator*(const BigInteger& a, const BigInteger& b) {
    BigInteger temp = a;
    temp *= b;
    return temp;
}

BigInteger operator/(const BigInteger& a, const BigInteger& b) {
    BigInteger temp = a;
    temp /= b;
    return temp;
}

BigInteger operator%(const BigInteger& a, const BigInteger& b) {
    BigInteger temp = a;
    temp %= b;
    return temp;
}

bool operator==(const BigInteger& a, const BigInteger& b) {
    if (a.size() != b.size()) {
        return false;
    }
    if (a.sign() != b.sign()) {
        return false;
    }
    for (size_t i = 0; i < a.size(); ++i) {
        if (a[i] != b[i]) {
            return false;
        }
    }
    return true;
}

bool operator!=(const BigInteger& a, const BigInteger& b) {
    return !(a == b);
}

bool operator<(const BigInteger& a, const BigInteger& b) {
    if (a.sign() != b.sign()) {
        return a.sign() < b.sign();
    }
    bool is_opp = false;
    if (a.sign() == -1) {
        is_opp = true;
    }
    if (a.size() != b.size()) {
        return a.size() < b.size();
    }
    for (int i = a.size() - 1; i >= 0; --i) {
        if (a[i] < b[i]) {
            return (true ^ is_opp) != 0;
        }
        if (a[i] > b[i]) {
            return (false ^ is_opp) != 0;
        }
    }
    return false;
}

bool operator>(const BigInteger& a, const BigInteger& b) {
    return b < a;
}

bool operator<=(const BigInteger& a, const BigInteger& b) {
    return !(a > b);
}

bool operator>=(const BigInteger& a, const BigInteger& b) {
    return !(a < b);
}

BigInteger::operator bool() const {
    return !(digits_.size() == 1 && digits_[0] == 0);
}

std::istream& operator>>(std::istream& in, BigInteger& x) {
    x.clear();
    std::string str;
    char symb;
    in.get(symb);
    while ((std::isspace(symb) != 0) && in.good()) {
        in.get(symb);
    }
    while ((!std::isspace(symb, in.getloc())) && in.good()) {
        str += symb;
        in.get(symb);
    }
    x = str;
    return in;
}

std::ostream& operator<<(std::ostream& out, const BigInteger& x) {
    std::string to_out = x.toString();
    out << to_out;
    return out;
}

void swap_bigInts(BigInteger& x, BigInteger& y) {
    std::swap(y.sz_, x.sz_);
    std::swap(y.sgn, x.sgn);
    std::swap(y.digits_, x.digits_);
}

void Rational::swap_rational(Rational& x) {
    std::swap(sgn, x.sgn);
    swap_bigInts(a_, x.a_);
    swap_bigInts(b_, x.b_);
    if (a_ == 0) {
        sgn = 1;
    }
}

BigInteger gcd(BigInteger x, BigInteger y) {
    while (y) {
        x %= y;
        swap_bigInts(x, y);
    }
    return x;
}

Rational::Rational() : a_(0), b_(1) {}

Rational::Rational(const BigInteger& x) : a_(x), b_(1) {
    if (a_.sign() == -1) {
        sgn = -1;
        a_.change_sign(1);
    }
}

Rational::Rational(long long x) : a_(x), b_(1) {
    if (a_.sign() == -1) {
        sgn = -1;
        a_.change_sign(1);
    }
}

Rational::Rational(int x) : a_(x), b_(1) {
    if (a_.sign() == -1) {
        sgn = -1;
        a_.change_sign(1);
    }
}

Rational Rational::operator-() const {
    if (a_.size() == 1 && a_[0] == 0) {
        return *this;
    }
    Rational copy = *this;
    copy.sgn *= -1;
    return copy;
}

std::string Rational::toString() const {
    std::string res;
    if (sgn == -1) {
        res = "-";
    }
    res += a_.toString();
    if (b_ != 1) {
        res += "/" + b_.toString();
    }
    return res;
}

std::string Rational::asDecimalToString(const BigInteger& beforeDot,
                                        const BigInteger& afterDot,
                                        size_t precision) {
    std::string res;
    res += beforeDot.toString() + ".";
    std::string resAfterDot = afterDot.toString();
    std::string missing(precision - resAfterDot.size(), '0');
    resAfterDot = missing + resAfterDot;
    res += resAfterDot;
    return res;
}

std::string Rational::asDecimal(size_t precision) const {
    BigInteger tmp1;
    std::string pw(precision, '0');
    pw = "1" + pw;
    BigInteger x(pw);
    tmp1.change_sign(sgn);
    tmp1 = tmp1.sign() * (a_ / b_);
    if (precision == 0) {
        return tmp1.toString();
    }
    BigInteger tmp2;
    tmp2 = (a_ % b_) * (x) / b_;
    return asDecimalToString(tmp1, tmp2, precision);
}

Rational::operator double() const {
    std::string s = asDecimal(20);
    return std::stod(s);
}

int Rational::sign() const {
    return sgn;
}
void Rational::cutTheFraction(Rational& nw) {
    BigInteger gc = gcd(nw.a_, nw.b_);
    nw.a_ /= gc;
    nw.b_ /= gc;
    swap_rational(nw);
}

void Rational::oppositeForWholeFractionIfNeeded(Rational& nw, BigInteger& x) {
    if (x.sign() == -1) {
        x.change_sign(-x.sign());
        nw.sgn *= -1;
    }
}

void Rational::oppositeForNumeratorOrDenomimatorIfNeeded(BigInteger& x) {
    if (x.sign() == -1) {
        x.change_sign(-x.sign());
    }
}

Rational& Rational::operator+=(const Rational& x) {
    Rational nw(1);
    nw.a_ = sgn * a_ * x.b_ + x.sgn * b_ * x.a_;
    oppositeForWholeFractionIfNeeded(nw, nw.a_);
    nw.b_ = b_ * x.b_;
    oppositeForWholeFractionIfNeeded(nw, nw.b_);
    cutTheFraction(nw);
    return *this;
}

Rational& Rational::operator-=(const Rational& x) {
    Rational nw(1);
    nw.a_ = sgn * a_ * x.b_ - x.sgn * b_ * x.a_;
    oppositeForWholeFractionIfNeeded(nw, nw.a_);
    nw.b_ = b_ * x.b_;
    oppositeForWholeFractionIfNeeded(nw, nw.b_);
    cutTheFraction(nw);
    return *this;
}

Rational& Rational::operator*=(const Rational& x) {
    Rational nw(1);
    nw.sgn = sgn * x.sgn;
    nw.a_ = a_ * x.a_;
    oppositeForNumeratorOrDenomimatorIfNeeded(nw.a_);
    nw.b_ = b_ * x.b_;
    oppositeForNumeratorOrDenomimatorIfNeeded(nw.b_);
    cutTheFraction(nw);
    return *this;
}

Rational& Rational::operator/=(const Rational& x) {
    Rational nw(1);
    nw.sgn = sgn * x.sgn;
    nw.a_ = a_ * x.b_;
    oppositeForNumeratorOrDenomimatorIfNeeded(nw.a_);
    nw.b_ = b_ * x.a_;
    oppositeForNumeratorOrDenomimatorIfNeeded(nw.b_);
    cutTheFraction(nw);
    return *this;
}

Rational operator+(const Rational& a, const Rational& b) {
    Rational temp = a;
    temp += b;
    return temp;
}

Rational operator-(const Rational& a, const Rational& b) {
    Rational temp = a;
    temp -= b;
    return temp;
}

Rational operator*(const Rational& a, const Rational& b) {
    Rational temp = a;
    temp *= b;
    return temp;
}

Rational operator/(const Rational& a, const Rational& b) {
    Rational temp = a;
    temp /= b;
    return temp;
}

const BigInteger& Rational::getNumerator() const {
    return a_;
}

const BigInteger& Rational::getDenominator() const {
    return b_;
}

Rational abs(const Rational& a) {
    if (a.sign() == 1) {
        return a;
    } else {
        return -a;
    }
}

bool operator==(const Rational& a, const Rational& b) {
    return (a.getNumerator() == b.getNumerator() &&
            a.getDenominator() == b.getDenominator() && a.sign() == b.sign());
}

bool operator<(const Rational& a, const Rational& b) {
    return (a.sign() * a.getNumerator() * b.getDenominator() <
            b.sign() * a.getDenominator() * b.getNumerator());
}

bool operator!=(const Rational& a, const Rational& b) {
    return !(a == b);
}

bool operator>(const Rational& a, const Rational& b) {
    return b < a;
}
bool operator<=(const Rational& a, const Rational& b) {
    return !(a > b);
}

bool operator>=(const Rational& a, const Rational& b) {
    return !(a < b);
}

std::istream& operator>>(std::istream& is, Rational& q) {
    BigInteger x;
    is >> x;
    q.a_ = x;
    return is;
}

std::ostream& operator<<(std::ostream& os, const Rational& q) {
    os << q.asDecimal(5);
    return os;
}
