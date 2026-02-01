import ModelChecking.LTL_NBW_Statement
import ModelChecking.LTL_NNF
import ModelChecking.NNF_ABW
import ModelChecking.ABW_NBW

theorem for_any_LTL_formula_exists_an_equivalent_NBW : for_any_LTL_formula_exists_an_equivalent_NBW_statement := by
  unfold for_any_LTL_formula_exists_an_equivalent_NBW_statement
  intros _ φ
  obtain ⟨_, _, A, lang_eq⟩ := exists_ABW_lang_for_LTL φ
  exists A.toNBW
  rw [lang_eq]
  rw [ABW.toNBW.lang_eq]

#print axioms for_any_LTL_formula_exists_an_equivalent_NBW
