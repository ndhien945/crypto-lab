#include <iostream>
#include <tuple>
#include <string>
#include <type_traits>

// --- Example struct ---
struct Point { int x, y; };

// --- Convert struct to tuple ---
template <typename T> struct as_tuple;

template <>
struct as_tuple<Point> {
    using type = std::tuple<int,int>;
    static type get(const Point& p) { return std::make_tuple(p.x, p.y); }
};

// --- Tuple printer (C++11, no index_sequence) ---
template <std::size_t I, typename Tuple>
struct tuple_printer {
    static void print(const Tuple& t) {
        tuple_printer<I - 1, Tuple>::print(t);
        std::cout << ", " << std::get<I>(t);
    }
};

template <typename Tuple>
struct tuple_printer<0, Tuple> {
    static void print(const Tuple& t) {
        std::cout << std::get<0>(t);
    }
};

template <typename Tuple>
void printTuple(const Tuple& t) {
    static const std::size_t N = std::tuple_size<Tuple>::value;
    if (N == 0) return;
    tuple_printer<N - 1, Tuple>::print(t);
}

// --- printValue ---
template <typename T>
typename std::enable_if<std::is_arithmetic<T>::value, void>::type
printValue(const T& v) {
    std::cout << v;
}

inline void printValue(const std::string& v) { std::cout << v; }
inline void printValue(const char* v) { std::cout << v; }

template <typename T>
typename std::enable_if<
    !std::is_arithmetic<T>::value &&
    !std::is_same<T, std::string>::value &&
    !std::is_same<T, const char*>::value,
    void>::type
printValue(const T& v) {
    using Tup = typename as_tuple<T>::type;
    printTuple(as_tuple<T>::get(v));
}

// --- custom_printf ---
inline void custom_printf(const char* format) {
    std::cout << format;
}

template <typename T, typename... Args>
void custom_printf(const char* format, const T& value, const Args&... args) {
    while (*format) {
        if (*format == '%' && *(format + 1)) {
            ++format;
            if (*format == 'd' || *format == 'f' || *format == 's') {
                printValue(value);
            } else if (*format == 'C' && *(format + 1) == 'd') {
                ++format;
                printValue(value);
            } else {
                std::cout << '%' << *format;
            }
            ++format;
            custom_printf(format, args...);
            return;
        }
        std::cout << *format++;
    }
}

// --- Test ---
int main() {
    int a = 42;
    std::string s = "hello";
    Point p{10, 20};

    custom_printf("%d %s %Cd\n", a, s, p);  // 42 hello 10, 20
}
