theorem apply_cond (f : α → β) (b : Bool) (x y : α) :
    f (cond b x y) = cond b (f x) (f y) := by cases b <;> rfl
