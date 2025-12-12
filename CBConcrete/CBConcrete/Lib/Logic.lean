@[simp, grind =]
theorem getElem_dite {coll idx elem valid} [GetElem coll idx elem valid] (P : Prop)
    [Decidable P] (f : P → coll) (g : ¬ P → coll)
    {k : idx} {hk : valid (if h : P then f h else g h) k} :
    (if h : P then f h else g h)[k] =
    if h : P then (f h)[k]'(by grind) else (g h)[k]'(by grind) := by grind

@[simp, grind =]
theorem getElem_ite {coll idx elem valid} [GetElem coll idx elem valid] (P : Prop)
    [Decidable P] (f g : coll)
    {k : idx} {hk : valid (if P then f else g) k} :
    (if P then f else g)[k] =
    if h : P then f[k]'(by grind) else g[k]'(by grind) := getElem_dite _ _ _

@[simp, grind =]
theorem dite_getElem {coll idx elem valid} [GetElem coll idx elem valid] (P : Prop)
    [Decidable P] (f : P → idx) (g : ¬ P → idx)
    {v : coll} {hk : valid v (if h : P then f h else g h)} :
    v[if h : P then f h else g h] =
    if h : P then v[f h]'(by grind) else v[g h]'(by grind) := by grind

@[simp, grind =]
theorem ite_getElem {coll idx elem valid} [GetElem coll idx elem valid] (P : Prop)
    [Decidable P] (f g : idx)
    {v : coll} {hk : valid v (if P then f  else g)} :
    v[if P then f else g] =
    if h : P then v[f]'(by grind) else v[g]'(by grind) := dite_getElem _ _ _

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
