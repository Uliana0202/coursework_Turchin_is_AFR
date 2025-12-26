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

* **Почти полное отношение:**  
  Интуиция: невозможно писать цепочку бесконечно долго так, чтобы каждое новое слово было "совершенно новым" и никак не было связано с предыдущими.  
  И вот почти полное отношение - такое отношение, что в любой бесконечной цепочке найдутся два таких слова, которые связаны этим отношением.
  ```coq
  Definition almost_full (R : word -> word -> Prop) : Prop :=
    forall (f : nat -> word),
      chain f -> 
      exists i j, i < j /\ R (f i) (f j).
  ```
  

Я хочу доказать, что отношение "Турчинской пары"  - это как раз почти полное отношение.

## `Repetition_Is_Turchin.v`  
Файл содержит ответ на вопросы: почему ограниченная последовательность обязана зациклиться и почему повтор слова приведет к паре Турчина.

* **Принцип Дирихле:**
  В общем: Если мы распределяем бесконечное количество предметов (индексы $n \in \mathbb{N}$) по конечному числу ящиков (список слов $L$), то хотя бы в один ящик попадет более одного предмета.  
  У меня: Если все значения функции $f$ принадлежат конечному списку $L$, то существуют $i < j$, такие что $f(i) = f(j)$.
  ```coq
  Lemma Infinite_Pigeonhole :
    forall (L : list (word letter)) (f : nat -> word letter),
    (forall n, In (f n) L) ->
    exists i j, i < j /\ f i = f j.
  ```

* **Конечность множества слов:**  
  Алфавит $\Sigma$ конечен, поэтому количество слов, длина которых не превышает некоторого $N$, конечно.

  Были определены "генераторы" слов длинны n (`generate_words_of_length`) и слов длинны от 0 до n (`generate_words_upto_length`) и доказана их полнота (то есть там **все** слова таких длин).
  
* **Гарантированность повтора:**  
  Если длины слов в цепочке ограничены, то в цепочке гарантированно есть повтор $f(i) = f(j)$.
  
  Идея: множество всех возможных слов длины не более Bound конечно, тогда по принципу Дирихлев любой бесконечной последовательности таких слов будут повторы.
  ```coq
  Lemma Bounded_Chain_Has_Repetition : 
    forall (f : nat -> word letter) (Bound : nat),
    (forall n, length (f n) <= Bound) -> 
    exists i j, i < j /\ f i = f j.
  ```
* **Есть повтор -> Пара Турчина**
  
  ```coq
  Lemma Repetition_Is_Turchin : 
  forall (f : nat -> word letter) (i j : nat),
  chain G f -> i < j -> f i <> [] -> f i = f j ->    
  is_turchin_pair G f i j.
  ```

  Идея:  
  $f(i) = f(i) ++ []$ - $\omega_i = v\omega'$.  
  $f(j) = f(i) ++ [] ++ []$ - $\omega_j = v v' \omega'$.

## `Turchin_Growth.v`
Файл доказывает появление пар Турчина при бесконечном рост длины слов.

* **Нижняя ватерлиния (LWM):**
  Индекс $k$ является LWM, если длина слова в этот момент является минимальной для всего будущего времени.

  ```coq
  Definition is_low_water_mark (f : nat -> word letter) (k : nat) : Prop :=
    forall t, t >= k -> length (f t) >= length (f k).
  ```
* **Существование LWM:**
  Если последовательность неограниченно растет, то для любого момента времени start_idx можно найти такой будущий момент $k \ge start\_idx$, который будет являться LWM.

  ```coq
  Lemma exists_LWM :
    forall f, chain G f ->
    (forall N, exists i, forall j, j > i -> length (f j) > N) ->
    forall start_idx, exists k, k >= start_idx /\ is_low_water_mark f k.
  ```

  Идея: рассматриваем множество всех длин слов $f(t)$ при $t \ge start\_idx$. Это множество натуральных чисел, и у него есть минимум. Момент времени $k$, когда этот минимум достигается, и есть искомый LWM.

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
  1. Так как последовательность бесконечно растет, то существет $k$, после которого длина слов никогда не станет меньше, чем $|f(k)|$. Выбирем такое $k$, чтобы слово было непустым (длина $> M=1$).
  2. В момент $k$ слово $f(k)$ можно разделить на голову (первую букву $l$) и хвост ($\text{suffix}$). При этом суффикс будет сохраняться, а правила переписывания будут затрагивать только голову.
  3. То есть у нас бесконечная последовательность слов, у которых общий общий хвост. Используем принцип Дирихле.
  4. Собираем пару Турчина $f(i)$ и $f(j)$  
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
## `Main.v`
  Собственно, к чему это мы...
  * **Turchin_AFR_Complete:**
  ```coq
  Theorem Turchin_AFR_Complete : 
    forall (f : nat -> word letter),
    chain G f ->
    (forall n, f n <> []) -> 
    is_Turchin_AFR f.
  ```
  Идея:  
  От противного: пусть, существует плохая бесконечная последовательность (в которой нет пар Турчина).
  1. Используем Bad_Sequence_Is_Bounded, существует граница длины Bound.
  2. Используем теорему Bounded_Chain_Has_Repetition, существуют повторения.
  3. Используем лемму Repetition_Is_Turchin, существует пара Турчина.

## Запуск

```
rm *.vo *.vok *.vos *.glob 
coq_makefile -f _CoqProject -o Makefile
make
```
При необходимости, перезагрузите окно (Ctrl+Shift+P и Developer: Reload Window).
