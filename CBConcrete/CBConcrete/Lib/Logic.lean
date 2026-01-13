@[simp, grind =]
theorem getElem_dite {coll idx elem valid} [GetElem coll idx elem valid] (P : Prop)
    [Decidable P] (a : P → coll) (b : ¬ P → coll)
    {k : idx} {hk : valid (if h : P then a h else b h) k} :
    (if h : P then a h else b h)[k] =
    if h : P then (a h)[k]'(by grind) else (b h)[k]'(by grind) := by grind

@[simp, grind =]
theorem getElem_ite {coll idx elem valid} [GetElem coll idx elem valid] (P : Prop)
    [Decidable P] (a b : coll)
    {k : idx} {hk : valid (if P then a else b) k} :
    (if P then a else b)[k] =
    if h : P then a[k]'(by grind) else b[k]'(by grind) := getElem_dite _ _ _

@[simp, grind =]
theorem dite_getElem {coll idx elem valid} [GetElem coll idx elem valid] (P : Prop)
    [Decidable P] (i : P → idx) (j : ¬ P → idx)
    {v : coll} {hk : valid v (if h : P then i h else j h)} :
    v[if h : P then i h else j h] =
    if h : P then v[i h]'(by grind) else v[j h]'(by grind) := by grind

@[simp, grind =]
theorem ite_getElem {coll idx elem valid} [GetElem coll idx elem valid] (P : Prop)
    [Decidable P] (i j : idx)
    {v : coll} {hk : valid v (if P then i else j)} :
    v[if P then i else j] =
    if h : P then v[i]'(by grind) else v[j]'(by grind) := dite_getElem _ _ _

@[simp]
theorem exists_or_index (P Q : Prop) (f : P ∨ Q → Prop) :
    (∃ (h : P ∨ Q), f h) ↔ (∃ (hp : P), f (by grind)) ∨ ∃ (hq : Q), f (by grind) := by grind

theorem dite_and {α} (P Q : Prop) [Decidable P] [Decidable Q] (f : P ∧ Q → α)
  (g : ¬ (P ∧ Q) → α) : (if h : P ∧ Q then f h else g h) =
  if hp : P then if hq : Q then f (by grind) else g (by grind) else g (by grind) := by grind

theorem dite_and_right {α} (P Q : Prop) [Decidable P] [Decidable Q] (f : P ∧ Q → α)
  (g : ¬ (P ∧ Q) → α) : (if h : P ∧ Q then f h else g h) =
  if hp : Q then if hq : P then f (by grind) else g (by grind) else g (by grind) := by grind

theorem dite_or {α} (P Q : Prop) [Decidable P] [Decidable Q] (f : P ∨ Q → α)
  (g : ¬ (P ∨ Q) → α) : (if h : P ∨ Q then f h else g h) =
  if hp : P then f (Or.inl hp) else if hq : Q then f (Or.inr hq) else g (by grind) := by grind

theorem dite_or_right {α} (P Q : Prop) [Decidable P] [Decidable Q] (f : P ∨ Q → α)
  (g : ¬ (P ∨ Q) → α) : (if h : P ∨ Q then f h else g h) =
  if hq : Q then f (Or.inr hq) else if hp : P then f (Or.inl hp) else g (by grind) := by grind

theorem ite_and_right {α} (P Q : Prop) [Decidable P] [Decidable Q] (a b : α) :
  (if P ∧ Q then a else b) = if Q then if P then a else b else b := by grind

theorem ite_or_right {α} (P Q : Prop) [Decidable P] [Decidable Q] (a b : α) :
  (if P ∨ Q then a else b) =
  if Q then a else if P then a else b := by grind
