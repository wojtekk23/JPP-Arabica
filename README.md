# Język Arabica

Język Arabica jest imperatywnym językiem wzorowanym na języku Latte.

## Struktura programu

Tak samo jak w języku Latte, programy w języku Arabica są listami funkcji. Każda taka lista musi zawierać funkcję `main`, która zwraca `int` i nie przyjmuje argumentów. Każda funkcja nie zwracająca `void` musi zawierać wyrażenie `return`.

Zmienne są wiązane statycznie.

## Instrukcje

* Pętle `while` i `for` (ze zmiennymi *read-only*) z wyrażeniami `break` i `continue`
* Wyrażenia `if`
* Bloki - zmienne zadeklarowane w bloku są widoczne tylko w bloku i przesłaniają zmienne o tej samej nazwie spoza bloku. W obrębie bloku zmienne muszą mieć unikalne nazwy.
* Zmienne muszą być zadeklarowane przed użyciem. Zmienna, która nie jest inicjalizowana podczas deklaracji, przyjmuje wartość domyślną (0 dla `int`, "" dla `string` i `false` dla `bool`)
* Wszystkie argumenty funkcji (również anonimowych) są przekazywane przez wartość

## Typy

* Typy `int`, `bool` i `string` odpowiadają takim samym typom z C++
* `void` służy do podkreślenia, że funkcja nie zwraca wartości
* Funkcje anonimowe (patrz: `correct3.ara`, `correct4.ara`) - zmienne z otaczającego zasięgu są pobierane przez wartość (tak jak capture `[=]` w C++)
* Brak niejawnej konwersji między typami.
* Tablice ustalonego rozmiaru (przyjmuje literał liczbowy, nie wyrażenie), indeksowane od 0

## Wyrażenia

* Wyrażenia logiczne są obliczane leniwie
* Reszta jak w języku Latte