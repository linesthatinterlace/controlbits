namespace List

universe u v

variable {α : Type u}

@[elab_as_elim]
def reverseRecOn {motive : List α → Sort v} (xs : List α) (nil : motive [])
    (append_singleton : ∀ (xs : List α) (x : α), motive xs → motive (xs ++ [x])) : motive xs :=
  match hxs : xs.length with
  | 0 => eq_nil_of_length_eq_zero hxs ▸ nil
  | n + 1 => dropLast_concat_getLast (ne_nil_of_length_eq_add_one hxs) ▸
    append_singleton _ _ (xs.dropLast.reverseRecOn nil append_singleton)
  termination_by xs.length

@[simp]
theorem reverseRecOn_nil {motive : List α → Sort v} (nil : motive [])
    (append_singleton : ∀ (xs : List α) (x : α), motive xs → motive (xs ++ [x])) :
  [].reverseRecOn nil append_singleton = nil := by grind [reverseRecOn]

@[simp]
theorem reverseRecOn_concat {motive : List α → Sort v} (nil : motive [])
    (append_singleton : ∀ (xs : List α) (x : α), motive xs → motive (xs ++ [x])) (xs : List α) (x : α) :
    (xs ++ [x]).reverseRecOn nil append_singleton =
    append_singleton xs x (xs.reverseRecOn nil append_singleton) := by
  grind [reverseRecOn]

@[elab_as_elim]
def reverseCases {motive : List α → Sort v} (nil : motive [])
    (append_singleton : ∀ (xs : List α) (x : α), motive (xs ++ [x])) (xs : List α) : motive xs :=
  xs.reverseRecOn nil (fun xs x _ => append_singleton xs x)

@[simp]
theorem reverseCases_nil {motive : List α → Sort v} (nil : motive [])
    (append_singleton : ∀ (xs : List α) (x : α), motive (xs ++ [x])) :
  reverseCases nil append_singleton [] = nil := by grind [reverseCases, reverseRecOn]

@[simp]
theorem reverseCases_concat {motive : List α → Sort v} (nil : motive [])
    (append_singleton : ∀ (xs : List α) (x : α), motive (xs ++ [x])) (xs : List α) (x : α) :
    reverseCases (motive := motive) nil append_singleton (xs ++ [x]) = append_singleton xs x := by
  grind [reverseCases, reverseRecOn]

theorem exists_getElem_cons (p : α → Prop) {c : List α} (b : α) {k : Nat}  :
    (∃ (hk : k < (b :: c).length), p (b :: c)[k]) ↔
    k = 0 ∧ p b ∨ ∃ (hk : 0 < k ∧ k - 1 < c.length), p c[k - 1] := by grind

theorem exists_getElem_push (p : α → Prop) {c : List α} (b : α) {k : Nat}  :
    (∃ (hk : k < (c ++ [b]).length), p (c ++ [b])[k]) ↔
    k = c.length ∧ p b ∨ ∃ (hk : k < c.length), p c[k] := by grind

theorem forall_getElem_push (p : α → Prop) {c : List α} (b : α) {k : Nat}  :
    (∀ (hk : k < (c ++ [b]).length), p (c ++ [b])[k]) ↔
    (k = c.length → p b) ∧ ∀ (hk : k < c.length), p c[k] := by grind

end List
