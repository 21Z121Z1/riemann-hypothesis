import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSplitFinMulSplitInf
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1448
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1460
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1447
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1456

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAutFormsWeightLevelLeTensorRange
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.TrKer

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def infHom (lam : InfinitePlace E → DomWeight n) : Submodule ℂ (Wsp lam →ₗ[ℂ] (UA E n → ℂ)) where
  carrier := {T | ∀ x ∈ infU E n, ∀ w, T (wInf lam x w) = RU E n x (T w)}
  add_mem' ha hb x hx w := by
    simp only [LinearMap.add_apply, ha x hx, hb x hx, map_add]
  zero_mem' x _ w := by simp
  smul_mem' c T hT x hx w := by
    simp only [LinearMap.smul_apply, hT x hx, map_smul]

theorem RU_mul (a b : UA E n) (φ : UA E n → ℂ) : RU E n (a * b) φ = RU E n a (RU E n b φ) := by
  rw [map_mul]; rfl

theorem comp_mem_infHom (lam : InfinitePlace E → DomWeight n) {T : Wsp lam →ₗ[ℂ] (UA E n → ℂ)} (hT : T ∈ infHom lam)
    (k : finU E n) : RU E n k.1 ∘ₗ T ∈ infHom lam := by
  intro x hx w
  simp only [LinearMap.comp_apply, hT x hx, ← RU_mul, GlobalTheory.DefU.fin_mul_inf k.2 hx]

theorem exists_op (lam : InfinitePlace E → DomWeight n) (A : Module.End ℂ (Wsp lam)) :
    ∃ P : Module.End ℂ (UA E n → ℂ), ∀ T ∈ infHom lam, ∀ w, T (A w) = P (T w) := by
  have hA : A ∈ Submodule.span ℂ (Set.range fun x : infU E n => wInf lam (x : UA E n)) := by
    rw [GlobalTheory.T.span_infinitePlacesWeightRepresentation_eq_top E n lam]; exact Submodule.mem_top
  induction hA using Submodule.span_induction with
  | mem A h =>
    obtain ⟨x, rfl⟩ := h
    exact ⟨RU E n x.1, fun T hT w => hT x.1 x.2 w⟩
  | zero => exact ⟨0, fun T _ w => by simp⟩
  | add A B _ _ hA hB =>
    obtain ⟨P, hP⟩ := hA
    obtain ⟨Q, hQ⟩ := hB
    exact ⟨P + Q, fun T hT w => by simp [hP T hT, hQ T hT]⟩
  | smul c A _ hA =>
    obtain ⟨P, hP⟩ := hA
    exact ⟨c • P, fun T hT w => by simp [hP T hT]⟩

theorem eq_zero_of_sum (lam : InfinitePlace E → DomWeight n) {ι : Type} [Fintype ι] (b : Module.Basis ι ℂ (Wsp lam))
    (T : ι → Wsp lam →ₗ[ℂ] (UA E n → ℂ)) (hT : ∀ j, T j ∈ infHom lam) (h : ∑ j, T j (b j) = 0) (k : ι) :
    T k = 0 := by
  refine b.ext fun m => ?_
  obtain ⟨P, hP⟩ := exists_op lam ((b.coord k).smulRight (b m))
  have := congrArg P h
  rw [map_sum, map_zero] at this
  rw [LinearMap.zero_apply, ← this]
  rw [Finset.sum_eq_single k]
  · rw [← hP _ (hT k)]; simp
  · intro j _ hj
    rw [← hP _ (hT j)]
    simp [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, hj]
  · simp

end GlobalTheory.BCT.TrKer

namespace GlobalTheory.BCT.TrKer

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem mem_span_values (lam : InfinitePlace E → DomWeight n) (π : Submodule ℂ (UA E n → ℂ)) (hπ : IsAutRepU π)
    (hW : ∀ v : InfinitePlace E, HasWeightAt π v.embedding (lam v)) {φ : UA E n → ℂ} (hφ : φ ∈ π) :
    φ ∈ Submodule.span ℂ {ψ | ∃ T ∈ infHom lam, (∀ w, T w ∈ π) ∧ ∃ w, T w = ψ} := by
  set Sv := Submodule.span ℂ {ψ | ∃ T ∈ infHom lam, (∀ w, T w ∈ π) ∧ ∃ w, T w = ψ}
  have hle : Sv ≤ π := Submodule.span_le.2 (by rintro _ ⟨T, -, hT, w, rfl⟩; exact hT w)
  have hst : ∀ g, ∀ ψ ∈ Sv, RU E n g ψ ∈ Sv := by
    intro g ψ hψ
    induction hψ using Submodule.span_induction with
    | mem ψ h =>
      obtain ⟨T, hT, hTπ, w, rfl⟩ := h
      rw [eq_splitFin_mul_splitInf g, RU_mul, ← hT _ (splitInf E n g).2]
      exact Submodule.subset_span ⟨_, comp_mem_infHom lam hT (splitFin E n g),
        fun w' => hπ.stable _ _ (hTπ w'), _, rfl⟩
    | zero => simp
    | add a c _ _ ha hc => rw [map_add]; exact add_mem ha hc
    | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha
  obtain ⟨T, hT0, hTπ, hT⟩ := GlobalTheory.T.exists_ne_zero_weightTensor_intertwining_autRep E n lam π hπ hW
  obtain ⟨w, hw⟩ := DFunLike.ne_iff.1 hT0
  rcases hπ.irred Sv hle hst with h | h
  · have hm : T w ∈ Sv := Submodule.subset_span ⟨T, hT, hTπ, w, rfl⟩
    rw [h, Submodule.mem_bot] at hm
    exact absurd hm hw
  · rw [h]; exact hφ

theorem mem_range_of_mem (S : Set (Pl E)) (K' : ∀ w : Pl E, Subgroup (UL n w)) (lam : InfinitePlace E → DomWeight n)
    (π : Submodule ℂ (UA E n → ℂ)) (hπ : IsAutRepU π) (hW : ∀ v : InfinitePlace E, HasWeightAt π v.embedding (lam v))
    {φ : UA E n → ℂ} (hφ : φ ∈ π) (hfix : φ ∈ fixed (RF E n) (globLev S K')) :
    φ ∈ LinearMap.range (Phi S lam K') := by
  classical
  let b := Module.finBasis ℂ (Wsp lam)
  have hdec : ∀ ψ ∈ Submodule.span ℂ {ψ | ∃ T ∈ infHom lam, (∀ w, T w ∈ π) ∧ ∃ w, T w = ψ},
      ∃ T : Fin (Module.finrank ℂ (Wsp lam)) → (Wsp lam →ₗ[ℂ] (UA E n → ℂ)),
        (∀ j, T j ∈ infHom lam) ∧ (∀ j w, T j w ∈ π) ∧ ψ = ∑ j, T j (b j) := by
    intro ψ hψ
    induction hψ using Submodule.span_induction with
    | mem ψ h =>
      obtain ⟨T, hT, hTπ, w, rfl⟩ := h
      refine ⟨fun j => b.repr w j • T, fun j => Submodule.smul_mem _ _ hT, fun j w' => π.smul_mem _ (hTπ w'), ?_⟩
      calc T w = T (∑ j, b.repr w j • b j) := by rw [b.sum_repr]
        _ = ∑ j, (b.repr w j • T) (b j) := by simp only [map_sum, map_smul, LinearMap.smul_apply]
    | zero => exact ⟨0, fun _ => zero_mem _, fun _ _ => π.zero_mem, by simp⟩
    | add a c _ _ ha hc =>
      obtain ⟨A, hA, hAπ, rfl⟩ := ha
      obtain ⟨C, hC, hCπ, rfl⟩ := hc
      exact ⟨A + C, fun j => add_mem (hA j) (hC j), fun j w => π.add_mem (hAπ j w) (hCπ j w),
        by simp [Finset.sum_add_distrib]⟩
    | smul c a _ ha =>
      obtain ⟨A, hA, hAπ, rfl⟩ := ha
      exact ⟨c • A, fun j => Submodule.smul_mem _ c (hA j), fun j w => π.smul_mem c (hAπ j w),
        by simp [Finset.smul_sum]⟩
  obtain ⟨T, hT, hTπ, rfl⟩ := hdec φ (mem_span_values lam π hπ hW hφ)
  have hfixT : ∀ k ∈ globLev S K', ∀ j, RU E n k.1 ∘ₗ T j = T j := by
    intro k hk j
    have h1 : RU E n k.1 (∑ j, T j (b j)) = ∑ j, T j (b j) := by
      have := hfix ⟨k, hk⟩
      simpa [RF] using this
    have h2 : ∑ i, (RU E n k.1 ∘ₗ T i - T i) (b i) = 0 := by
      simp only [LinearMap.sub_apply, LinearMap.comp_apply, Finset.sum_sub_distrib, ← map_sum, h1, sub_self]
    exact sub_eq_zero.1 (eq_zero_of_sum lam b _ (fun i => sub_mem (comp_mem_infHom lam (hT i) k) (hT i)) h2 j)
  obtain ⟨F, hFa⟩ : ∃ F : Fin (Module.finrank ℂ (Wsp lam)) → finU E n → Module.Dual ℂ (Wsp lam),
      ∀ j x w, F j x w = T j w x.1 :=
    ⟨fun j x => LinearMap.proj (R := ℂ) (φ := fun _ : UA E n => ℂ) x.1 ∘ₗ T j, fun _ _ _ => rfl⟩
  have hphi : ∀ j, phiFun lam (F j) = T j := by
    intro j
    refine LinearMap.ext fun w => funext fun g => ?_
    rw [phiFun_apply, hFa]
    have hg := eq_splitFin_mul_splitInf g
    have hw : wInf lam g = wInf lam (splitInf E n g).1 := by
      conv_lhs => rw [hg]
      rw [map_mul, wInf_fin, one_mul]
    rw [hw, hT j _ (splitInf E n g).2]
    change T j w ((splitFin E n g).1 * (splitInf E n g).1) = T j w g
    rw [← hg]
  have hF : ∀ j, F j ∈ vecM S lam K' := by
    intro j
    refine ⟨fun γ x => ?_, fun k hk x => ?_⟩
    · refine LinearMap.ext fun w => ?_
      rw [LinearMap.dualMap_apply, hFa, hFa]
      obtain ⟨r, hr, hrf, hrc⟩ := GlobalTheory.T.exists_definiteUnitaryRationalPoint_finite_and_infinite_parts E n γ
      set i := splitInf E n r
      have hri : r = (finPt γ).1 * i.1 := by rw [← hrf]; exact eq_splitFin_mul_splitInf r
      have hc : ∀ v : InfinitePlace E, cEmb v.embedding (i.1⁻¹) = GeneralLinearGroup.map v.embedding (γ⁻¹).1 := by
        intro v
        have : i.1⁻¹ = r⁻¹ * (finPt γ).1 := by rw [hri]; group
        rw [this, map_mul, map_inv, hrc v, cEmb_fin, mul_one, Subgroup.coe_inv, map_inv]
      have hwi : wInf lam i.1⁻¹ = wAt lam γ⁻¹ := by
        change PiTensorProduct.map (fun v => GlobalTheory.Branching.sqRep ℂ n (lam v) (cEmb v.embedding i.1⁻¹)) = _
        unfold wAt
        simp only [hc]
      have hl := (hπ.aut _ (hTπ j w)).left r hr (i.1⁻¹ * x.1)
      rw [← hwi, hT j _ (inv_mem i.2)]
      change T j w ((finPt γ).1 * x.1) = T j w (x.1 * i.1⁻¹)
      rw [GlobalTheory.DefU.fin_mul_inf x.2 (inv_mem i.2), ← hl, hri]
      congr 1
      group
    · refine LinearMap.ext fun w => ?_
      rw [hFa, hFa]
      change T j w (x.1 * k.1) = T j w x.1
      exact congrFun (LinearMap.congr_fun (hfixT k hk j) w) x.1
  refine ⟨∑ j, ⟨F j, hF j⟩ ⊗ₜ b j, ?_⟩
  simp [map_sum, Phi_tmul, hphi]

theorem forms_le_range : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → forms S lam K' ≤ LinearMap.range (Phi S lam K') := by
  intro E _ _ _ _ n _ S _ lam K' _
  refine iSup_le fun π => iSup_le fun hπ => ?_
  rintro φ ⟨hφ, hfix⟩
  exact mem_range_of_mem S K' lam π hπ.1 hπ.2 hφ hfix

end GlobalTheory.BCT.TrKer

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepPureTensorLocal
section
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

noncomputable section

namespace GlobalTheory.FinComm.RhoPure

variable {F : Type} [Field F] [NumberField F]

theorem eq_single_of_ann (v : Pl F) (a : AF F) (h : ∀ u : AF F, evFin F v u = 0 → u * a = 0) :
    a = LinearMap.inr F (Ainf F) (Af F) (singleFin v (evFin F v a)) := by
  set e : AF F := LinearMap.inr F (Ainf F) (Af F) (singleFin v 1) with he_def
  have he : evFin F v e = 1 := evalV_singleFin_self v 1
  have h1 : (1 - e) * a = 0 := h _ (by rw [map_sub, map_one, he, sub_self])
  have hea : a = e * a := by linear_combination h1
  have key : e * a = LinearMap.inr F (Ainf F) (Af F) (singleFin v (evFin F v (e * a))) := by
    refine Prod.ext ?_ ?_
    · show (0 : Ainf F) * a.1 = 0
      exact zero_mul _
    · show singleFin v 1 * a.2 = singleFin v (evFin F v (e * a))
      apply af_ext
      intro u
      rw [map_mul]
      by_cases hu : u = v
      · subst hu
        rw [evalV_singleFin_self, evalV_singleFin_self, one_mul]
        show evalV F u a.2 = evalV F u (singleFin u 1 * a.2)
        rw [map_mul, evalV_singleFin_self, one_mul]
      · rw [evalV_singleFin_ne hu, evalV_singleFin_ne hu, zero_mul]
  rw [← hea] at key
  exact key

theorem mulSupport_finite {κ : Type} [Finite κ] (φ : ∀ u : Pl F, (κ → Fv F u) → ℂ)
    (hφ : ∀ᶠ u in cofinite, φ u = GlobalTheory.FinComm.indO u) (y : κ → AF F) :
    (Function.mulSupport fun u : Pl F => φ u fun i => evFin F u (y i)).Finite := by
  have h2 : ∀ᶠ u : Pl F in cofinite, ∀ i, evFin F u (y i) ∈ u.adicCompletionIntegers F :=
    Filter.eventually_all.2 fun i => (y i).2.2
  have h3 : ∀ᶠ u : Pl F in cofinite, (φ u fun i => evFin F u (y i)) = 1 := by
    filter_upwards [hφ, h2] with u hu hu2
    rw [hu]
    exact Set.indicator_of_mem (s := {x : κ → Fv F u | ∀ i, x i ∈ u.adicCompletionIntegers F}) hu2 _
  exact Filter.eventually_cofinite.1 h3

theorem finprod_update_mul {ι : Type} (g : ι → ℂ) (hg : (Function.mulSupport g).Finite) (v : ι) (c : ℂ) :
    ∏ᶠ u, Function.update g v (c * g v) u = c * ∏ᶠ u, g u := by
  have hg' : (Function.mulSupport (Function.update g v (c * g v))).Finite :=
    (hg.insert v).subset fun u hu => by
      by_cases h : u = v
      · exact Or.inl h
      · exact Or.inr (by rwa [Function.mem_mulSupport, Function.update_of_ne h] at hu)
  rw [← mul_finprod_cond_ne v hg', ← mul_finprod_cond_ne v hg, Function.update_self, mul_assoc]
  congr 2
  apply finprod_congr; intro u; apply finprod_congr; intro h; exact Function.update_of_ne h _ _

theorem rho_pure_tensor {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (v : Pl F)
    (w : Matrix (Fin n) (Fin d) (AE F E)) (hw : At (evFin F v) w)
    (f : SInf F (Fin n × Fin d)) (φ : ∀ u : Pl F, (Fin n × Fin d → Fv F u) → ℂ)
    (hφ : ∀ᶠ u in cofinite, φ u = GlobalTheory.FinComm.indO u) :
    M.co.rho ψ w (pure f φ) =
      pure f (Function.update φ v (GlobalTheory.FinComm.locOp ψ v (GlobalTheory.FinComm.locPt v (M.co.e w)) (φ v))) := by
  funext x
  simp only [Darboux.rho, schr, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Pi.add_apply]
  set p := M.co.e w with hp_def
  have hp : ∀ u : AF F, evFin F v u = 0 → u • p = 0 := by
    intro u hu
    rw [hp_def, ← map_smul, hw u hu, map_zero]
  have h1 : ∀ i, p.1 i = LinearMap.inr F (Ainf F) (Af F) (singleFin v (evFin F v (p.1 i))) := fun i =>
    eq_single_of_ann v _ fun u hu => congrArg (fun q => q.1 i) (hp u hu)
  have hfst : ∀ i, (p.1 i).1 = 0 := fun i => congrArg Prod.fst (h1 i)
  have hsnd : ∀ i, (p.1 i).2 = singleFin v (evFin F v (p.1 i)) := fun i => congrArg Prod.snd (h1 i)
  have hI : ∀ i, evI F (x i + p.1 i) = evI F (x i) := by
    intro i
    unfold evI
    congr 1
    show (x i).1 + (p.1 i).1 = (x i).1
    rw [hfst, add_zero]
  have hFne : ∀ u, u ≠ v → ∀ i, evFin F u (x i + p.1 i) = evFin F u (x i) := by
    intro u hu i
    rw [map_add]
    show _ + evalV F u (p.1 i).2 = _
    rw [hsnd, evalV_singleFin_ne hu, add_zero]
  have hp2 : ∀ u : AF F, evFin F v u = 0 → u • p.2 = 0 := fun u hu => congrArg Prod.snd (hp u hu)
  set s : AF F := x ⬝ᵥ p.2 + ⅟(2 : AF F) * (p.1 ⬝ᵥ p.2) with hs
  have hs1 : s = LinearMap.inr F (Ainf F) (Af F) (singleFin v (evFin F v s)) := by
    apply eq_single_of_ann
    intro u hu
    have e1 : u * (x ⬝ᵥ p.2) = 0 := by rw [← smul_eq_mul, ← dotProduct_smul, hp2 u hu, dotProduct_zero]
    have e2 : u * (p.1 ⬝ᵥ p.2) = 0 := by rw [← smul_eq_mul, ← dotProduct_smul, hp2 u hu, dotProduct_zero]
    rw [hs]
    linear_combination e1 + ⅟(2 : AF F) * e2
  have h2' : evFin F v (⅟(2 : AF F)) = 2⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← map_ofNat (evFin F v) 2, ← map_mul, invOf_mul_self, map_one]
  have hev : evFin F v s = (fun i => evFin F v (x i)) ⬝ᵥ (GlobalTheory.FinComm.locPt v p).2 +
      (GlobalTheory.FinComm.locPt v p).1 ⬝ᵥ (GlobalTheory.FinComm.locPt v p).2 / 2 := by
    rw [hs]
    simp only [GlobalTheory.FinComm.locPt, dotProduct, map_add, map_mul, map_sum, h2']
    try ring
  set g : Pl F → ℂ := fun u => φ u fun i => evFin F u (x i + p.1 i) with hg
  have hfin : (Function.mulSupport g).Finite := mulSupport_finite φ hφ (x + p.1)
  have hprod : (fun u => Function.update φ v (GlobalTheory.FinComm.locOp ψ v (GlobalTheory.FinComm.locPt v p) (φ v)) u
      fun i => evFin F u (x i)) = Function.update g v (ψ s * g v) := by
    funext u
    rcases eq_or_ne u v with rfl | hu
    · rw [Function.update_self, Function.update_self]
      simp only [GlobalTheory.FinComm.locOp, hg]
      conv_rhs => rw [hs1]
      rw [hev]
      congr 1
    · rw [Function.update_of_ne hu, Function.update_of_ne hu, hg]
      simp only [hFne u hu]
  rw [hprod, finprod_update_mul g hfin v (ψ s)]
  simp only [hI]
  ring

theorem rho_pure : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (v : Pl F)
    (w : Matrix (Fin n) (Fin d) (AE F E)), At (evFin F v) w →
    ∀ (f : SInf F (Fin n × Fin d)) (φ : ∀ u : Pl F, (Fin n × Fin d → Fv F u) → ℂ),
      (∀ᶠ u in cofinite, φ u = GlobalTheory.FinComm.indO u) →
      M.co.rho ψ w (pure f φ) =
        pure f (Function.update φ v (GlobalTheory.FinComm.locOp ψ v (GlobalTheory.FinComm.locPt v (M.co.e w)) (φ v))) :=
  fun M ψ v w hw f φ hφ => rho_pure_tensor M ψ v w hw f φ hφ

end GlobalTheory.FinComm.RhoPure
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameExtendsToBlockBasis
section
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

namespace GlobalTheory.SiegelSet.PerpBasis

theorem exists_ker_basis {E : Type} [Field E] {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι (Fin n) E) (B : Matrix (Fin n) ι E) (h : G * B * (G * B) = 1) :
    ∃ (n₀ : ℕ) (Z : Matrix (Fin n) (Fin n₀) E) (Q : Matrix (Fin n₀ ⊕ ι) (Fin n) E),
      n₀ + Fintype.card ι = n ∧ Q * Matrix.fromCols Z B = 1 ∧ Matrix.fromCols Z B * Q = 1 ∧ G * Z = 0 := by
  set K := LinearMap.ker G.mulVecLin with hK
  let b := Module.finBasis E K
  let Z : Matrix (Fin n) (Fin (Module.finrank E K)) E := Matrix.of fun i j => (b j : Fin n → E) i
  have hZv : ∀ a, Z *ᵥ a = ((∑ j, a j • b j : K) : Fin n → E) := by
    intro a
    ext i
    simp [Z, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hGZv : ∀ a, G *ᵥ (Z *ᵥ a) = 0 := by
    intro a
    rw [hZv]
    exact (∑ j, a j • b j : K).2
  have hGZ : G * Z = 0 := by
    ext i j
    have := congrFun (hGZv (Pi.single j 1)) i
    rw [Matrix.mulVec_mulVec] at this
    simpa using this
  have hsurj : LinearMap.range G.mulVecLin = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro v
    refine ⟨(B * (G * B)) *ᵥ v, ?_⟩
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]
    rw [← Matrix.mul_assoc, h, Matrix.one_mulVec]
  have hdim : Module.finrank E K + Fintype.card ι = n := by
    have := LinearMap.finrank_range_add_finrank_ker G.mulVecLin
    rw [hsurj] at this
    simp only [finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at this
    rw [hK]
    omega
  have hinj : Function.Injective (Matrix.toLin' (Matrix.fromCols Z B)) := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    rw [Matrix.toLin'_apply, Matrix.fromCols_mulVec] at hv
    have h1 : (G * B) *ᵥ (v ∘ Sum.inr) = 0 := by
      have := congrArg (G *ᵥ ·) hv
      simp only [Matrix.mulVec_add, hGZv, zero_add, Matrix.mulVec_zero] at this
      rw [← Matrix.mulVec_mulVec]; exact this
    have h2 : v ∘ Sum.inr = 0 := by
      have := congrArg ((G * B) *ᵥ ·) h1
      simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at this
      rwa [h, Matrix.one_mulVec] at this
    rw [h2, Matrix.mulVec_zero, add_zero, hZv] at hv
    have h3 : (∑ j, (v ∘ Sum.inl) j • b j : K) = 0 := Subtype.ext hv
    have h4 := Fintype.linearIndependent_iff.1 b.linearIndependent _ h3
    ext x
    rcases x with x | x
    · exact h4 x
    · exact congrFun h2 x
  let e := LinearMap.linearEquivOfInjective _ hinj (by simp [hdim])
  have he : (e : (Fin (Module.finrank E K) ⊕ ι → E) →ₗ[E] (Fin n → E)) =
      Matrix.toLin' (Matrix.fromCols Z B) := by
    ext1 x; rfl
  have he' : LinearMap.toMatrix' (e : (Fin (Module.finrank E K) ⊕ ι → E) →ₗ[E] (Fin n → E)) =
      Matrix.fromCols Z B := by rw [he, LinearMap.toMatrix'_toLin']
  refine ⟨_, Z, LinearMap.toMatrix' (e.symm : (Fin n → E) →ₗ[E] (Fin (Module.finrank E K) ⊕ ι → E)),
    hdim, ?_, ?_, hGZ⟩
  · rw [← he', ← LinearMap.toMatrix'_comp]; simp
  · rw [← he', ← LinearMap.toMatrix'_comp]; simp

section
variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)

theorem gram_eq_map (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {a b : Type}
    (A : Matrix (Fin n) a E) (B : Matrix (Fin n) b E) :
    Aᵀ * J * B.map σ = (Formalism.UG.cT (σ : E →+* E) A * ((1 : E) • J.map σ) * B).map σ := by
  ext i j
  simp [Formalism.UG.cT, Matrix.mul_apply, hσ]

theorem gram_eq_transpose {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (hJ : ∀ i j, σ (J j i) = J i j)
    {a b : Type} (A : Matrix (Fin n) a E) (B : Matrix (Fin n) b E) :
    Aᵀ * J * B.map σ = (Formalism.UG.cT (σ : E →+* E) B * ((1 : E) • J.map σ) * A)ᵀ := by
  have : J.map σ = Jᵀ := by ext i j; simp [hJ]
  rw [this]
  simp only [Formalism.UG.cT, one_smul, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.mul_assoc]
  rfl

end

theorem exists_perp_basis : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), (∀ i j, σ (J j i) = J i j) → J.det ≠ 0 →
    ∀ (r₀ : ℕ) (Xf Yf : Matrix (Fin n) (Fin r₀) E), GlobalTheory.SiegelSet.IsWittFrame σ ((1 : E) • J.map σ) Xf Yf →
    ∃ (n₀ : ℕ) (Z₀ : Matrix (Fin n) (Fin n₀) E) (Q : Matrix (Fin n₀ ⊕ (Fin r₀ ⊕ Fin r₀)) (Fin n) E),
      n₀ + (r₀ + r₀) = n ∧
      Q * Matrix.fromCols Z₀ (Matrix.fromCols Xf Yf) = 1 ∧ Matrix.fromCols Z₀ (Matrix.fromCols Xf Yf) * Q = 1 ∧
      (Matrix.fromCols Z₀ (Matrix.fromCols Xf Yf))ᵀ * J * (Matrix.fromCols Z₀ (Matrix.fromCols Xf Yf)).map σ =
        Matrix.fromBlocks (Z₀ᵀ * J * Z₀.map σ) 0 0 (Matrix.fromBlocks 0 1 1 0) ∧
      (Z₀ᵀ * J * Z₀.map σ).det ≠ 0 ∧ (∀ i j, σ ((Z₀ᵀ * J * Z₀.map σ) j i) = (Z₀ᵀ * J * Z₀.map σ) i j) ∧
      Formalism.UG.cT (σ : E →+* E) Xf * ((1 : E) • J.map σ) * Z₀ = 0 ∧ Formalism.UG.cT (σ : E →+* E) Yf * ((1 : E) • J.map σ) * Z₀ = 0 := by
  intro F E _ _ _ _ _ σ hcm n J hJ hdet r₀ X Y hW
  have hσ : ∀ x, σ (σ x) = x := GlobalTheory.SiegelSet.sigma_sigma hcm
  have gxx : Xᵀ * J * X.map σ = 0 := by rw [gram_eq_transpose σ J hJ, hW.xx]; simp
  have gyy : Yᵀ * J * Y.map σ = 0 := by rw [gram_eq_transpose σ J hJ, hW.yy]; simp
  have gyx : Yᵀ * J * X.map σ = 1 := by rw [gram_eq_transpose σ J hJ, hW.xy]; simp
  have gxy : Xᵀ * J * Y.map σ = 1 := by
    rw [gram_eq_map σ hσ J, hW.xy]; exact Matrix.map_one _ (map_zero σ) (map_one σ)
  have hyx : Formalism.UG.cT (σ : E →+* E) Y * ((1 : E) • J.map σ) * X = 1 := by
    have := gram_eq_transpose σ J hJ X Y
    rw [gxy] at this
    rw [← Matrix.transpose_transpose (_ * X), ← this, Matrix.transpose_one]
  have hGB : Matrix.fromRows (Formalism.UG.cT (σ : E →+* E) X * ((1 : E) • J.map σ))
      (Formalism.UG.cT (σ : E →+* E) Y * ((1 : E) • J.map σ)) * Matrix.fromCols X Y =
      Matrix.fromBlocks 0 1 1 0 := by
    rw [Matrix.fromRows_mul_fromCols, hW.xx, hW.yy, hW.xy, hyx]
  obtain ⟨n₀, Z, Q, hn, hQP, hPQ, hGZ⟩ := exists_ker_basis
    (Matrix.fromRows (Formalism.UG.cT (σ : E →+* E) X * ((1 : E) • J.map σ))
      (Formalism.UG.cT (σ : E →+* E) Y * ((1 : E) • J.map σ))) (Matrix.fromCols X Y)
    (by rw [hGB, Matrix.fromBlocks_multiply]; simp)
  rw [Matrix.fromRows_mul] at hGZ
  have hXZ : Formalism.UG.cT (σ : E →+* E) X * ((1 : E) • J.map σ) * Z = 0 := by
    ext i j; exact congrFun (congrFun hGZ (Sum.inl i)) j
  have hYZ : Formalism.UG.cT (σ : E →+* E) Y * ((1 : E) • J.map σ) * Z = 0 := by
    ext i j; exact congrFun (congrFun hGZ (Sum.inr i)) j
  have gzx : Zᵀ * J * X.map σ = 0 := by rw [gram_eq_transpose σ J hJ, hXZ]; simp
  have gzy : Zᵀ * J * Y.map σ = 0 := by rw [gram_eq_transpose σ J hJ, hYZ]; simp
  have gxz : Xᵀ * J * Z.map σ = 0 := by
    rw [gram_eq_map σ hσ J, hXZ]; exact Matrix.map_zero _ (map_zero σ)
  have gyz : Yᵀ * J * Z.map σ = 0 := by
    rw [gram_eq_map σ hσ J, hYZ]; exact Matrix.map_zero _ (map_zero σ)
  have hgram : (Matrix.fromCols Z (Matrix.fromCols X Y))ᵀ * J *
      (Matrix.fromCols Z (Matrix.fromCols X Y)).map σ =
      Matrix.fromBlocks (Zᵀ * J * Z.map σ) 0 0 (Matrix.fromBlocks 0 1 1 0) := by
    simp only [Matrix.transpose_fromCols, Matrix.fromCols_map]
    rw [Matrix.fromRows_mul, Matrix.fromRows_mul_fromCols, Matrix.fromRows_mul,
      Matrix.fromRows_mul_fromCols, Matrix.mul_fromCols, Matrix.fromRows_mul,
      gxx, gyy, gyx, gxy, gzx, gzy, gxz, gyz]
    simp
  refine ⟨n₀, Z, Q, by simpa using hn, hQP, hPQ, hgram, ?_, ?_, hXZ, hYZ⟩
  · set P := Matrix.fromCols Z (Matrix.fromCols X Y) with hP
    have hJu : IsUnit J.det := hdet.isUnit
    have h1 : P.map σ * Q.map σ = 1 := by
      rw [← Matrix.map_mul, hPQ]; exact Matrix.map_one _ (map_zero σ) (map_one σ)
    have h2 : Pᵀ * Qᵀ = 1 := by rw [← Matrix.transpose_mul, hQP, Matrix.transpose_one]
    have h3 : (Pᵀ * J * P.map σ) * (Q.map σ * J⁻¹ * Qᵀ) = 1 := by
      calc _ = Pᵀ * (J * ((P.map σ * Q.map σ) * J⁻¹)) * Qᵀ := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [h1, Matrix.one_mul, Matrix.mul_nonsing_inv _ hJu, Matrix.mul_one, h2]
    have h4 := congrArg Matrix.det h3
    rw [Matrix.det_mul, hgram, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one] at h4
    intro h0
    rw [h0] at h4
    simp at h4
  · intro i j
    have h1 := congrFun (congrFun (gram_eq_map σ hσ J Z Z) j) i
    have h2 := congrFun (congrFun (gram_eq_transpose σ J hJ Z Z) i) j
    rw [h1, h2, Matrix.map_apply, hσ, Matrix.transpose_apply]

end GlobalTheory.SiegelSet.PerpBasis
end

