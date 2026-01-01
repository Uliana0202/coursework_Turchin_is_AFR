# Формализация доказательства отношения Турчина как почти полного отношения на цепочках, порожденных префиксными грамматиками с конечным числом правилю.

## `Turchin_Defs.v`
Файл с базовыми определениями.  

* **Алфавит и Грамматика:**
  Определяется конечный алфавит letter и слова word (списки букв).
  Грамматика grammar - набор правил переписывания rule (буква заменяется на слово).
  ```coq
  Variable letter : Set.
  Variable letter_eq_dec : forall x y : letter, {x = y} + {x <> y}.
  
  Variable Finite_Sigma : list letter.
  Variable Is_Finite : forall x : letter, In x Finite_Sigma.
  
  Definition word := list letter.

  Definition rule := (letter * word)%type.

  Definition grammar := list rule.
  Variable G : grammar.
  ```

* **Шаг переписывания:**
  Заменяется буква l на слово rhs, а хвост tail сохраняется.
  ```coq
  Inductive step : word -> word -> Prop :=
    | step_intro : forall (l : letter) (rhs tail : word),
        In (l, rhs) G ->
        (* l :: tail - исходное слово  *)
        (* rhs ++ tail - новое слово *)
        step (l :: tail) (rhs ++ tail).
  ```
* **Цепочка слов:**
  ```coq
  Definition chain (f : nat -> word) : Prop :=
      forall n, step (f n) (f (S n)).
  ```
* **Неизменность суффикса:**
  ```coq
  Definition tail_preserved (f : nat -> word) (n : nat) (suffix : word) : Prop :=
      exists (l : letter) (rhs middle : word),
        In (l, rhs) G /\
        f n = l :: middle ++ suffix /\       (* до шага *)
        f (S n) = rhs ++ middle ++ suffix.   (* после шага *)
  ```

* **Пара Турчина:**
  Два слова $\omega_i$ и $\omega_j$ ($i < j$) образуют пару Турчина $\omega_i \triangleleft \omega_j$, если $\omega_i = v\omega'$ и $\omega_j = v v' \omega'$, где голова $v$ не пуста, а хвост $\omega'$  неизменен на всём отрезке цепочки от $i$ до $j-1$.  
  ```coq
  Definition is_turchin_pair (f : nat -> word) (i j : nat) : Prop :=
    i < j /\
    exists (v v' w' : word),
      v <> [] /\
      f i = v ++ w' /\
      f j = v ++ v' ++ w' /\
      (* w' неизменна на каждом шаге от i до j-1 *)
      (forall k, i <= k < j -> tail_preserved f k w').
  ```

## `Turchin_Lib.v`  
Вспомогательные леммы, в частности принцип Дирихле.
* **NoDup_nth_error_unique:**  
  В списке без повторов одно и то же значение не может находиться по двум разным индексам.
  ```coq
   Lemma NoDup_nth_error_unique : forall {A : Type} (l : list A) (i j : nat) (x : A),
    NoDup l ->
    nth_error l i = Some x ->
    nth_error l j = Some x ->
    i = j.
  ```
* **Сохранение уникальности при отображении:**  
  Если список l уникален, и мы применяем к нему инъективную функцию $f$, то результат map f l тоже будет уникальным.
  ```coq
    Lemma NoDup_map_injective : forall (A B : Type) (f : A -> B) (l : list A),
      (forall x y, In x l -> In y l -> f x = f y -> x = y) ->
      NoDup l -> NoDup (map f l).
  ```
* **Свойства строго сортированных списков:**    
  1. В возрастающем списке любой элемент меньше или равен последнему.
     ```coq
      Lemma sorted_last_max : forall (h : nat) (t : list nat) (d : nat),
        Sorted lt (h :: t) ->
        forall z, In z (h :: t) -> z <= last (h :: t) d.
     ```
  2. Добавление более крупного элемента в конец отсортированного списка сохраняет сортировку.
     ```coq
      Lemma sorted_snoc_max : forall (l : list nat) (x : nat),
        Sorted lt l ->
        (forall y, In y l -> y < x) ->
        Sorted lt (l ++ [x]).
     ```
  3. Если элементы в списке строго возрастают ($x_1 < x_2 < \dots$), то среди них гарантированно нет дубликатов.
     
     ```coq
     Lemma Sorted_lt_implies_NoDup : forall l, Sorted lt l -> NoDup l.
     ```
 
* **Принцип Дирихле (конечный):**  
  В общем: Если голуби рассажены в клетки, причём число голубей больше числа клеток, то хотя бы в одной из клеток находится более одного голубя.  
  У меня: Если длина списка индексов $l$ превышает размер алфавита $|\Sigma|$, и мы отображаем каждый индекс в букву алфавита ($f\_{map}$), то неизбежно повторение.
  ```coq
   Lemma Pigeonhole_Finite_Sigma : forall (A : Type) (l : list A) (f_map : A -> letter),
    NoDup l ->
    length l > length Finite_Sigma ->
    exists x y, In x l /\ In y l /\ x <> y /\ f_map x = f_map y.
  ```
  
* **Принцип Дирихле (бесконечный):**  
  В общем: Если мы распределяем бесконечное количество предметов (индексы $n \in \mathbb{N}$) по конечному числу ящиков (список слов $L$), то хотя бы в один ящик попадет более одного предмета.  
  У меня: Если все значения функции $f$ принадлежат конечному списку $L$, то существуют $i < j$, такие что $f(i) = f(j)$.
  ```coq
  Lemma Infinite_Pigeonhole :
    forall (L : list (word letter)) (f : nat -> word letter),
    (forall n, In (f n) L) ->
    exists i j, i < j /\ f i = f j.
  ```

## `Turchin_Growth.v`
Файл доказывает появление пар Турчина при бесконечном рост длины слов.  

* **Нижняя ватерлиния (LWM):**  
  Индекс $k$ является LWM, если длина слова в этот момент является минимальной для всего будущего времени.

  ```coq
  Definition is_low_water_mark (f : nat -> word letter) (k : nat) : Prop :=
    forall t, t >= k -> length (f t) >= length (f k).
  ```
* **Существование LWM:**  
  Если последовательность неограниченно растет, то для любого момента времени $start_{idx}$ можно найти такой будущий момент $k \ge start_{idx}$, который будет являться LWM.

  ```coq
  Lemma exists_LWM :
    forall f, chain G f ->
    (forall N, exists i, forall j, j > i -> length (f j) > N) ->
    forall start_idx, exists k, k >= start_idx /\ is_low_water_mark f k.
  ```

  Идея: рассматриваем множество всех длин слов $f(t)$ при $t \ge start\_{idx}$. Это множество натуральных чисел, и у него есть минимум. Момент времени $k$, когда этот минимум достигается, и есть искомый LWM.  

  Более того, можно найти LWM, где длина слова будет строго больше, чем раньше.
  ```coq
  Lemma exists_next_growing_LWM :
    forall f k,
    chain G f ->
    (forall N, exists i, forall j, j > i -> length (f j) > N) ->
    is_low_water_mark f k ->
    exists k', k' > k /\ length (f k') > length (f k) /\ is_low_water_mark f k'.
  ```
* **Сохранение суффика:**  
  Если k — LWM, и f(k) = l :: suffix, то suffix сохраняется навсегда.
  ```coq
  Lemma preserves_suffix_forever :
    forall f k l suffix,
    chain G f ->
    is_low_water_mark f k ->
    f k = l :: suffix ->
    forall t, t >= k -> exists prefix, f t = prefix ++ suffix.
  ```
  Идея:
  1. База: $t=k$
  2. В момент $t$ слово имеет вид $p :: \text{suffix}$. Делаем шаг к $t+1$.
     Если правило затрагивает суффикс,то префикс $p$ исчезает, и мы начинаем переписывать суффикс. Тогда общая длина слова становится меньше длины $f(k)$ (так как $|f(k)| = 1 + |\text{suffix}|$). Это противоречит определению LWM (длина не может падать ниже $|f(k)|$).

* **Теорема о росте (Моих слез):**  
  Если последовательность растет неограниченно, в ней обязана возникнуть пара Турчина.

  ```coq
  Theorem Growth_Implies_Turchin_Pair :
    forall f,
    chain G f ->
    (forall n, f n <> []) ->
    (* неограниченный рост *)
    (forall N, exists i, forall j, j > i -> length (f j) > N) ->
    exists i j, is_turchin_pair G f i j.
  ```

  Идея:  
  1. Строим бесконечную последовательность индексов LWM $k_1, k_2, \dots$, такую что длины слов строго растут: $|f(k_1)| < |f(k_2)| < \dots$.
  2. Берем первые $|\Sigma| + 1$ таких индексов и смотрим на первые буквы слов $f(k_m)$.
  3. По принципу Дирихле (`Pigeonhole_Finite_Sigma`), среди $|\Sigma| + 1$ слов найдутся два слова $f(i)$ и $f(j)$ ($i < j$), начинающиеся с одинаковой буквы $h$.  
  4. Так как $i$ - это LWM, то хвост слова $f(i)$ сохраняется во времени и присутствует в $f(j)$.
  5. Получаем пару Турчина:  
     $f(i) = h :: \text{tail}$  
     $f(j) = h :: (\dots) :: \text{tail}$  


## `Main.v`
  Собственно, к чему это мы...
* **Генераторы слов:**  
  Были определены "генераторы" слов длинны n (`generate_words_of_length`) и слов длинны от 0 до n (`generate_words_upto_length`) и доказана их полнота (то есть там **все** слова таких длин). Полнота в будущем даст конечность множества "Universe".

* **Гарантированность повтора:**  
  Если длины слов в цепочке ограничены, то в цепочке гарантированно есть повтор $f(i) = f(j)$.
  
  ```coq
  Lemma Bounded_Chain_Has_Repetition : 
    forall (f : nat -> word letter) (Bound : nat),
    (forall n, length (f n) <= Bound) -> 
    exists i j, i < j /\ f i = f j.
  ```
   Идея: множество всех возможных слов длины не более Bound конечно, тогда по принципу Дирихле (`Infinite_Pigeonhole`) в любой бесконечной последовательности таких слов будут повторы.
  
* **Связь повтора и отношения Турчина:**  
  ```coq
  Lemma Repetition_Is_Turchin : 
  forall (f : nat -> word letter) (i j : nat),
  chain G f -> i < j -> f i <> [] -> f i = f j ->    
  is_turchin_pair G f i j.
  ```

  Идея:  
  $f(i) = f(i) ++ []$ - $\omega_i = v\omega'$.  
  $f(j) = f(i) ++ [] ++ []$ - $\omega_j = v v' \omega'$.

* **Плохая последовательность:**
  ```coq
  Definition IsBadSequence (f : nat -> word letter) : Prop :=
  forall i j, i < j -> ~ is_turchin_pair G f i j.
  ```

* **Ограниченность плохой последовательности:**
  Длины всех слов в плохой последовательности, порожденной неукорачивающей грамматикой, ограничены некоторой константой Bound.

  ```coq
  Theorem Bad_Sequence_Is_Bounded :
    forall f,
    chain G f ->
    (forall n, f n <> []) ->
    IsBadSequence f ->
    exists Bound, forall n, length (f n) <= Bound.
  ```
  
  Идея: От противного. Последовательность плохая, но не ограниченная, тогда по теореме моих слез в ней есть пара Турчина, противоречие.

* **Определение AFR:**  
  Интуиция: невозможно писать цепочку бесконечно долго так, чтобы каждое новое слово было "совершенно новым" и никак не было связано с предыдущими.  
  И вот почти полное отношение - такое отношение, что в любой бесконечной цепочке найдутся два таких слова, которые связаны этим отношением.
 
  ```coq
  Definition Relation_is_AFR (Rel : (nat -> word letter) -> nat -> nat -> Prop) : Prop :=
    forall (f : nat -> word letter),
    chain G f ->                 
    (forall n, f n <> []) ->     
    exists i j, i < j /\ Rel f i j.
  ```
* **Turchin_AFR_Complete:**
  Отношение "Турчинской пары"  - это почти полное отношение.
  ```coq
   Theorem Turchin_is_AFR : Relation_is_AFR (is_turchin_pair G).
  ```
  Идея:  
  1. От противного: существует плохая последовательность.  
  2. Если последовательность плохая, то она ограничена (`Bad_Sequence_Is_Bounded`).  
  3. Если последовательность ограничена, то по Принципу Дирихле (`Infinite_Pigeonhole`) в ней неизбежен повтор.
  4. Если есть повтор, то существует пара Турчина (`Repetition_Is_Turchin`).
  5. Противоречие.  
  
## Запуск

```
rm *.vo *.vok *.vos *.glob 
coq_makefile -f _CoqProject -o Makefile
make
```
При необходимости, перезагрузите окно (Ctrl+Shift+P и Developer: Reload Window).
