import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0196
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0182
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0205
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0198
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0200
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0201
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsStandardIndModule

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFockPolynomialIsoUnitaryPair
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.RealIt.PolyIso

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix

theorem sgn_mul_self (x : Bool) : sgn x * sgn x = 1 := by cases x <;> simp [sgn]

variable {p q r s a b : ℕ} (ε : Fin a → Bool) (ε' : Fin b → Bool) (e : Ix p q ≃ Fin a) (e' : Ix r s ≃ Fin b)

def fwd : LPol b a →ₐ[ℂ] Pol p q r s :=
  aeval fun v => sgn (ε v.2) • (X (e.symm v.2, e'.symm v.1) : Pol p q r s)

def bwd : Pol p q r s →ₐ[ℂ] LPol b a :=
  aeval fun l => sgn (ε (e l.1)) • (X (e' l.2, e l.1) : LPol b a)

theorem fwd_X (c : Ix r s) (x : Ix p q) :
    fwd ε e e' (X (e' c, e x)) = sgn (ε (e x)) • (X (x, c) : Pol p q r s) := by
  simp [fwd]

def kap : LPol b a ≃ₐ[ℂ] Pol p q r s :=
  AlgEquiv.ofAlgHom (fwd ε e e') (bwd ε e e')
    (by
      apply MvPolynomial.algHom_ext
      rintro ⟨x, c⟩
      simp [fwd, bwd, smul_smul, sgn_mul_self])
    (by
      apply MvPolynomial.algHom_ext
      rintro ⟨i, j⟩
      simp [fwd, bwd, smul_smul, sgn_mul_self])

theorem pderiv_fwd (c : Ix r s) (x : Ix p q) (P : LPol b a) :
    pderiv (x, c) (fwd ε e e' P) = sgn (ε (e x)) • fwd ε e e' (pderiv (e' c, e x) P) := by
  induction P using MvPolynomial.induction_on with
  | C z => simp [fwd]
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P v hP =>
    obtain ⟨i, j⟩ := v
    obtain ⟨d, rfl⟩ := e'.surjective i
    obtain ⟨y, rfl⟩ := e.surjective j
    have h : pderiv (x, c) (fwd ε e e' (X (e' d, e y))) =
        sgn (ε (e x)) • fwd ε e e' (pderiv (e' c, e x) (X (e' d, e y) : LPol b a)) := by
      rw [fwd_X, Derivation.map_smul, pderiv_X, pderiv_X]
      by_cases hx : x = y
      · by_cases hc : c = d
        · subst hx hc; simp
        · simp [Ne.symm hc]
      · simp [Ne.symm hx]
    rw [map_mul, Derivation.leibniz, Derivation.leibniz, h, hP]
    simp only [smul_eq_mul, map_add, map_mul, smul_add, mul_smul_comm]

variable {ε ε' e e'}

theorem linePos_iff (h : SignCompat ε e) (h' : SignCompat ε' e') (x : Ix p q) (c : Ix r s) :
    linePos ((x, c) : Ln p q r s) = true ↔ ε' (e' c) = ε (e x) := by
  rw [h x, h' c]
  rcases x with x | x <;> rcases c with c | c <;> simp [linePos]

theorem fwd_mulX (c : Ix r s) (x : Ix p q) (P : LPol b a) :
    fwd ε e e' (sgn (ε (e x)) • (X (e' c, e x) * P)) = X (x, c) * fwd ε e e' P := by
  rw [map_smul, map_mul, fwd_X, smul_mul_assoc, smul_smul, sgn_mul_self, one_smul]

theorem fwd_rai (h : SignCompat ε e) (h' : SignCompat ε' e') (x : Ix p q) (c : Ix r s) (P : LPol b a) :
    fwd ε e e' (rai ε ε' (e' c) (e x) P) = raiB (x, c) (fwd ε e e' P) := by
  unfold rai raiB
  by_cases hl : ε' (e' c) = ε (e x)
  · rw [if_pos hl, if_pos ((linePos_iff h h' x c).2 hl)]
    exact fwd_mulX c x P
  · rw [if_neg hl, if_neg (mt (linePos_iff h h' x c).1 hl)]
    simp [pderiv_fwd]

theorem fwd_low (h : SignCompat ε e) (h' : SignCompat ε' e') (x : Ix p q) (c : Ix r s) (P : LPol b a) :
    fwd ε e e' (low ε ε' (e' c) (e x) P) = lowB (x, c) (fwd ε e e' P) := by
  unfold low lowB
  by_cases hl : ε' (e' c) = ε (e x)
  · rw [if_pos hl, if_pos ((linePos_iff h h' x c).2 hl)]
    simp [pderiv_fwd]
  · rw [if_neg hl, if_neg (mt (linePos_iff h h' x c).1 hl)]
    exact fwd_mulX c x P

theorem act_eq_sum {V : Type*} [AddCommGroup V] [Module ℂ V] (f : Mat p q →ₗ[ℂ] V) (Z : Mat p q) :
    f Z = ∑ x, ∑ y, Z x y • f (Eab x y) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single Z]
  simp only [map_sum, ← map_smul, Eab, Matrix.smul_single, smul_eq_mul, mul_one]

theorem fwd_locS (h : SignCompat ε e) (h' : SignCompat ε' e') (Z : Mat p q) (P : LPol b a) :
    fwd ε e e' (locS ε ε' (Matrix.reindex e e Z) P) = fockAct1 p q r s Z (fwd ε e e' P) := by
  rw [act_eq_sum (fockAct1 p q r s) Z, locS, ← e.sum_comp]
  simp only [LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← e.sum_comp]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [fockAct1_Eab, ← e'.sum_comp]
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum, Matrix.reindex_apply,
    Matrix.submatrix_apply, Equiv.symm_apply_apply]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [omE, LinearMap.add_apply, map_add, Module.End.mul_apply, fwd_rai h h', fwd_low h h']
  congr 1
  by_cases hxy : x = y <;> simp [hxy]

theorem fwd_locT (h : SignCompat ε e) (h' : SignCompat ε' e') (Z : Mat r s) (P : LPol b a) :
    fwd ε e e' (locT ε ε' (Matrix.reindex e' e' Z) P) = fockAct2 p q r s Z (fwd ε e e' P) := by
  rw [act_eq_sum (fockAct2 p q r s) Z, locT, ← e'.sum_comp]
  simp only [LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← e'.sum_comp]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [fockAct2_Eab, ← e.sum_comp]
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum, Matrix.reindex_apply,
    Matrix.submatrix_apply, Equiv.symm_apply_apply]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [omE, LinearMap.add_apply, map_add, Module.End.mul_apply, fwd_rai h h', fwd_low h h']
  congr 1
  by_cases hcd : c = d <;> simp [hcd]

theorem exists_isPolyIso : ∀ (p q r s a b : ℕ) (ε : Fin a → Bool) (ε' : Fin b → Bool) (e : Ix p q ≃ Fin a)
    (e' : Ix r s ≃ Fin b), GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.SignCompat ε e → GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.SignCompat ε' e' →
    ∃ κ : LPol b a ≃ₗ[ℂ] Pol p q r s, IsPolyIso ε ε' e e' κ :=
  fun _ _ _ _ _ _ ε _ e e' h h' =>
    ⟨(kap ε e e').toLinearEquiv, fun Z P => fwd_locS h h' Z P, fun Z P => fwd_locT h h' Z P⟩

end GlobalTheory.Chain.RealIt.PolyIso

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGlobalFockIntertwinerTensorRealPlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Chain.RealIt.TensorGlob

theorem der_span {E : Type*} [AddCommGroup E] [Module ℂ E] {s : Set E} (hs : Submodule.span ℂ s = ⊤)
    (f : ℝ → E →ₗ[ℂ] ℂ) (g : E →ₗ[ℂ] ℂ) (h : ∀ e ∈ s, HasDerivAt (fun t => f t e) (g e) 0) (e : E) :
    HasDerivAt (fun t => f t e) (g e) 0 := by
  have he : e ∈ Submodule.span ℂ s := hs ▸ Submodule.mem_top
  induction he using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero =>
    have h0 : (fun t => f t 0) = fun _ => (0 : ℂ) := funext fun t => map_zero (f t)
    rw [h0, map_zero]
    exact hasDerivAt_const _ _
  | add x y _ _ hx hy =>
    have h0 : (fun t => f t (x + y)) = fun t => f t x + f t y := funext fun t => map_add (f t) x y
    rw [h0, map_add]
    exact hx.add hy
  | smul a x _ hx =>
    have h0 : (fun t => f t (a • x)) = fun t => a * f t x := funext fun t => map_smul (f t) a x
    rw [h0, map_smul, smul_eq_mul]
    exact hx.const_mul a

theorem der_span₂ {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    {s : Set E} (hs : Submodule.span ℂ s = ⊤) {s' : Set F} (hs' : Submodule.span ℂ s' = ⊤)
    (f : ℝ → E →ₗ[ℂ] F →ₗ[ℂ] ℂ) (g : E →ₗ[ℂ] F →ₗ[ℂ] ℂ)
    (h : ∀ e ∈ s, ∀ x ∈ s', HasDerivAt (fun t => f t e x) (g e x) 0) (e : E) (x : F) :
    HasDerivAt (fun t => f t e x) (g e x) 0 := by
  have h1 : ∀ x ∈ s', ∀ e', HasDerivAt (fun t => f t e' x) (g e' x) 0 := fun x hx e' =>
    der_span hs (fun t => (f t).flip x) (g.flip x) (fun e'' he'' => h e'' he'' x hx) e'
  exact der_span hs' (fun t => f t e) (g e) (fun x hx => h1 x hx e) x

variable {D : D7}

open Classical in
theorem glue_update {a b : ℕ} (P : D.what₂.Tau → LPol b a) (τ : D.what₂.Tau) (p : LPol b a) :
    glue (Function.update P τ p) = MvPolynomial.rename (fun s => (τ, s)) p *
      ∏ ρ ∈ Finset.univ.erase τ, MvPolynomial.rename (fun s => (ρ, s)) (P ρ) := by
  unfold glue
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ τ)]
  congr 1
  · simp
  · exact Finset.prod_congr rfl fun ρ hρ => by simp [Finset.ne_of_mem_erase hρ]

open Classical in
theorem glue_update_add_smul {a b : ℕ} (P : D.what₂.Tau → LPol b a) (τ : D.what₂.Tau) (p : LPol b a) (c : ℂ) :
    glue (Function.update P τ p) + c • glue P = glue (Function.update P τ (p + c • P τ)) := by
  have h0 : glue P = glue (Function.update P τ (P τ)) := by rw [Function.update_eq_self]
  rw [h0, glue_update, glue_update, glue_update, map_add, map_smul, add_mul, smul_mul_assoc]

variable {V : HSp D} {S : D.what₂.Tau → SPar}

theorem ellT_tprod' (M : DSModel V S) (w v : ∀ τ, M.H τ) :
    ellT M w (PiTensorProduct.tprod ℂ v) = ∏ τ, ⟪w τ, v τ⟫_ℂ := by
  unfold ellT
  rw [PiTensorProduct.lift.tprod]
  simp

open Classical in
theorem ellT_update (M : DSModel V S) (w v : ∀ τ, M.H τ) (τ : D.what₂.Tau) (u : M.H τ) :
    ellT M w (PiTensorProduct.tprod ℂ (Function.update v τ u)) =
      ⟪w τ, u⟫_ℂ * ∏ ρ ∈ Finset.univ.erase τ, ⟪w ρ, v ρ⟫_ℂ := by
  rw [ellT_tprod', ← Finset.mul_prod_erase _ _ (Finset.mem_univ τ)]
  congr 1
  · simp
  · exact Finset.prod_congr rfl fun ρ hρ => by simp [Finset.ne_of_mem_erase hρ]

open Classical in
theorem actT_tprod (M : DSModel V S) (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) (v : ∀ τ, M.H τ) :
    actT M τ g (PiTensorProduct.tprod ℂ v) = PiTensorProduct.tprod ℂ (Function.update v τ (M.rep τ g (v τ))) := by
  unfold actT
  rw [PiTensorProduct.map_tprod]
  congr 1
  funext ρ
  by_cases hρ : ρ = τ
  · subst hρ; simp
  · simp [Function.update_of_ne hρ]

theorem der_inner {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {c : ℝ → H} {y : H}
    (h : HasDerivAt c y 0) (w : H) (k : ℂ) : HasDerivAt (fun t => ⟪w, c t⟫_ℂ * k) (⟪w, y⟫_ℂ * k) 0 := by
  have h1 : HasDerivAt (fun t => ⟪w, c t⟫_ℂ) ⟪w, y⟫_ℂ 0 := by
    simpa [Function.comp_def] using ((innerSL ℂ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
  exact h1.mul_const k

open Classical in

theorem exists_globIt : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (aS aT : D.what₂.Tau → ℚ) (A : ∀ τ, LPol W.rank V.rank →ₗ[ℂ] M'.H τ →ₗ[ℂ] M.H τ), GlobalTheory.IndefiniteRowSideFullHecke.ContractionTensorModels.ContrTensor → GlueLaw D V.rank W.rank → (∀ τ, LocIt M M' τ (aS τ) (aT τ) (A τ)) → ∃ It I, GlobIt M M' aS aT It I := by
  intro D V W S S' M M' aS aT A hC hG hL
  have hs := hG.1
  have hs' : Submodule.span ℂ (Set.range (PiTensorProduct.tprod ℂ : (∀ τ, M'.H τ) → ⨂[ℂ] τ, M'.H τ)) = ⊤ :=
    PiTensorProduct.span_tprod_eq_top
  obtain ⟨I, hI, -⟩ := hC D.what₂.Tau (fun _ => Fin W.rank × Fin V.rank) (FVar D W.rank V.rank)
    (Equiv.sigmaEquivProd D.what₂.Tau (Fin W.rank × Fin V.rank) :
      (Σ _ : D.what₂.Tau, Fin W.rank × Fin V.rank) ≃ FVar D W.rank V.rank)
    (fun τ => M'.H τ) (fun τ => M.H τ) A
  have hIg : ∀ (P : D.what₂.Tau → LPol W.rank V.rank) (v : ∀ τ, M'.H τ),
      I (glue P) (PiTensorProduct.tprod ℂ v) = PiTensorProduct.tprod ℂ fun ρ => A ρ (P ρ) (v ρ) :=
    fun P v => hI P v
  let Itl : ∀ τ, LPol W.rank V.rank →ₗ[ℂ] M'.sm τ →ₗ[ℂ] M.sm τ := fun τ =>
    LinearMap.mk₂ ℂ (fun P y => (⟨A τ P (y : M'.H τ), (hL τ).sm P (y : M'.H τ)⟩ : M.sm τ))
      (fun P Q y => Subtype.ext (by simp)) (fun c P y => Subtype.ext (by simp))
      (fun P y z => Subtype.ext (by simp)) (fun c P y => Subtype.ext (by simp))
  have hItl : ∀ τ P y, ((Itl τ P y : M.sm τ) : M.H τ) = A τ P (y : M'.H τ) := fun _ _ _ => rfl
  obtain ⟨It, hIt, hItne⟩ := hC D.what₂.Tau (fun _ => Fin W.rank × Fin V.rank) (FVar D W.rank V.rank)
    (Equiv.sigmaEquivProd D.what₂.Tau (Fin W.rank × Fin V.rank) :
      (Σ _ : D.what₂.Tau, Fin W.rank × Fin V.rank) ≃ FVar D W.rank V.rank)
    (fun τ => ↥(M'.sm τ)) (fun τ => ↥(M.sm τ)) Itl
  have hItg : ∀ (P : D.what₂.Tau → LPol W.rank V.rank) (v : ∀ τ, M'.sm τ),
      It (glue P) (PiTensorProduct.tprod ℂ v) = PiTensorProduct.tprod ℂ fun ρ => Itl ρ (P ρ) (v ρ) :=
    fun P v => hIt P v
  have hupdP : ∀ (P : D.what₂.Tau → LPol W.rank V.rank) (τ : D.what₂.Tau) (Q : LPol W.rank V.rank)
      (v : ∀ τ, M'.H τ), (PiTensorProduct.tprod ℂ fun ρ => A ρ (Function.update P τ Q ρ) (v ρ)) =
        PiTensorProduct.tprod ℂ (Function.update (fun ρ => A ρ (P ρ) (v ρ)) τ (A τ Q (v τ))) := by
    intro P τ Q v
    congr 1
    funext ρ
    by_cases hρ : ρ = τ
    · subst hρ; simp
    · simp [Function.update_of_ne hρ]
  have hupdV : ∀ (P : D.what₂.Tau → LPol W.rank V.rank) (τ : D.what₂.Tau) (v : ∀ τ, M'.H τ) (y : M'.H τ),
      (PiTensorProduct.tprod ℂ fun ρ => A ρ (P ρ) (Function.update v τ y ρ)) =
        PiTensorProduct.tprod ℂ (Function.update (fun ρ => A ρ (P ρ) (v ρ)) τ (A τ (P τ) y)) := by
    intro P τ v y
    congr 1
    funext ρ
    by_cases hρ : ρ = τ
    · subst hρ; simp
    · simp [Function.update_of_ne hρ]
  refine ⟨It, I, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · intro φ v
    have h1 : It.compr₂ (inclT M) = I.compl₂ (inclT M') := by
      refine LinearMap.ext_on hs ?_
      rintro _ ⟨P, rfl⟩
      refine PiTensorProduct.ext (MultilinearMap.ext fun v => ?_)
      simp only [LinearMap.compMultilinearMap_apply, LinearMap.compr₂_apply, LinearMap.compl₂_apply, hItg]
      unfold inclT
      simp only [PiTensorProduct.map_tprod, Submodule.subtype_apply, hItl, hIg]
    exact DFunLike.congr_fun (DFunLike.congr_fun h1 φ) v
  · apply hItne
    intro τ h0
    obtain ⟨P, y, hy, hne⟩ := (hL τ).ne
    apply hne
    have h2 := congrArg (fun B : LPol W.rank V.rank →ₗ[ℂ] M'.sm τ →ₗ[ℂ] M.sm τ =>
      ((B P ⟨y, hy⟩ : M.sm τ) : M.H τ)) h0
    simpa [hItl] using h2
  · intro φ w
    have hφ : φ ∈ Submodule.span ℂ (Set.range (glue : (D.what₂.Tau → LPol W.rank V.rank) → PolF D W.rank V.rank)) :=
      hs ▸ Submodule.mem_top
    induction hφ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨P, rfl⟩ := hx
      choose w' hw' using fun τ => (hL τ).adj (P τ) (w τ)
      refine Submodule.subset_span ⟨w', ?_⟩
      refine PiTensorProduct.ext (MultilinearMap.ext fun v => ?_)
      simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, hIg, ellT_tprod', hw']
    | zero => simp
    | add x y _ _ hx hy =>
      rw [map_add, LinearMap.comp_add]
      exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      rw [map_smul, LinearMap.comp_smul]
      exact Submodule.smul_mem _ a hx
  · intro τ X hX φ x w
    have key := der_span₂ hs hs' (fun t => I.compr₂ (ellT M w ∘ₗ actT M τ (NormedSpace.exp (t • X))))
      ((I ∘ₗ srcOp M M' τ (aT τ) X).compr₂ (ellT M w)) ?hyp φ x
    · simpa only [LinearMap.compr₂_apply, LinearMap.comp_apply] using key
    case hyp =>
      rintro _ ⟨P, rfl⟩ _ ⟨v, rfl⟩
      simp only [LinearMap.compr₂_apply, LinearMap.comp_apply, srcOp, LinearMap.add_apply,
        LinearMap.smul_apply, Module.End.one_apply, (hG.2 τ (M.ε τ) (M'.ε τ) P).1, glue_update_add_smul,
        hIg, hupdP, actT_tprod, ellT_update]
      rw [neg_smul, ← sub_eq_add_neg]
      exact der_inner ((hL τ).src X hX (P τ) (v τ)) (w τ) _
  · intro τ Y hY φ x w
    have key := der_span₂ hs hs'
      (fun t => (I.compl₂ (actT M' τ (NormedSpace.exp (t • Y)))).compr₂ (ellT M w))
      (-((I ∘ₗ tgtOp M M' τ (aS τ) Y).compr₂ (ellT M w))) ?hyp φ x
    · simpa only [LinearMap.compr₂_apply, LinearMap.compl₂_apply, LinearMap.comp_apply,
        LinearMap.neg_apply] using key
    case hyp =>
      rintro _ ⟨P, rfl⟩ _ ⟨v, rfl⟩
      simp only [LinearMap.compr₂_apply, LinearMap.compl₂_apply, LinearMap.comp_apply, LinearMap.neg_apply,
        tgtOp, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
        (hG.2 τ (M.ε τ) (M'.ε τ) P).2, glue_update_add_smul, hIg, hupdP, hupdV, actT_tprod, ellT_update]
      rw [← neg_mul, ← inner_neg_right]
      exact der_inner ((hL τ).tgt Y hY (P τ) (v τ)) (w τ) _

end GlobalTheory.Chain.RealIt.TensorGlob

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIdempotentComponentOfGroupElement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GfCut

variable {R : Type} [CommRing R] {n : ℕ}

theorem idem_mul (φ : R) (hφ : φ * φ = φ) (A B : Matrix (Fin n) (Fin n) R)
    (h : A * B = 1) : (φ • A + (1 - φ) • (1 : Matrix (Fin n) (Fin n) R)) * (φ • B + (1 - φ) • 1) = 1 := by
  have h1 : φ * (1 - φ) = 0 := by rw [mul_sub, mul_one, hφ, sub_self]
  have h2 : (1 - φ) * φ = 0 := by rw [mul_comm, h1]
  have h3 : (1 - φ) * (1 - φ) = 1 - φ := by rw [mul_sub, mul_one, h2, sub_zero]
  simp only [add_mul, mul_add, smul_mul_smul_comm, h, h1, h2, h3, hφ, zero_smul, mul_one, add_zero, zero_add]
  rw [← add_smul, add_sub_cancel, one_smul]

theorem map_idem {T : Type} [CommRing T] (ψ : R →+* T) (f : R) (M : Matrix (Fin n) (Fin n) R) :
    (f • M + (1 - f) • (1 : Matrix (Fin n) (Fin n) R)).map ψ = ψ f • M.map ψ + (1 - ψ f) • 1 := by
  ext i j
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, map_add,
    map_mul, map_sub, map_one]
  split_ifs <;> simp

theorem idem_unitary (σ : R →+* R) (ε : R) (hε : σ ε = ε) (hεε : ε * ε = ε) (J M : Matrix (Fin n) (Fin n) R)
    (h : Formalism.UG.cT σ M * J * M = J) :
    Formalism.UG.cT σ (ε • M + (1 - ε) • (1 : Matrix (Fin n) (Fin n) R)) * J * (ε • M + (1 - ε) • 1) = J :=
  _root_.GlobalTheory.TruncationIsometry.cut_isometry σ ε hε hεε J M h

end GlobalTheory.GfCut

open GlobalTheory.GfCut in
theorem GlobalTheory.GfCut.exists_cut : ∀ {D : D7} (T : HSp D) (g : GA D T) (ε : AE D), g ∈ GfC T → ε * ε = ε → cA D ε = ε → ∃ k : GA D T, k ∈ GfC T ∧ Formalism.L2.Theta.mt T k = ε • Formalism.L2.Theta.mt T g + (1 - ε) • (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D)) := by
  intro D T g ε hg hεε hε
  set M := Formalism.L2.Theta.mt T g with hM
  have hinv : M * ((matHom T g)⁻¹).1 = 1 := (matHom T g).mul_inv
  have hinv' : ((matHom T g)⁻¹).1 * M = 1 := (matHom T g).inv_mul
  let K : GL (Fin T.rank) (AE D) := ⟨ε • M + (1 - ε) • 1, ε • ((matHom T g)⁻¹).1 + (1 - ε) • 1,
    idem_mul ε hεε _ _ hinv, idem_mul ε hεε _ _ hinv'⟩
  have hgU : Formalism.UG.cT (cA D) M * T.gram.map (incA D) * M = T.gram.map (incA D) :=
    (show HR (AF D.host.F) D.sp.cm.sig T.gram from g).2
  have hKU : K ∈ HR (AF D.host.F) D.sp.cm.sig T.gram :=
    idem_unitary (cA D) ε hε hεε _ M hgU
  let k : GA D T := (⟨K, hKU⟩ : HR (AF D.host.F) D.sp.cm.sig T.gram)
  refine ⟨k, ?_, rfl⟩
  have hg1 : infHom T g = 1 := hg
  show infHom T k = 1
  have hg2 := congrArg Units.val hg1
  apply Units.ext
  change (ε • M + (1 - ε) • (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D))).map _ = 1
  rw [map_idem]
  change M.map _ = 1 at hg2
  rw [hg2, ← add_smul, add_sub_cancel, one_smul]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntegralInverseOnConjugateHalf
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftLevel

namespace GlobalTheory.HalfUnit

theorem cc_star (D : D7) (x : D.host.E) : cc (star x) = x := by
  first
  | exact star_star x
  | rfl
  | simp [cc]

theorem mem_conjI_of (D : D7) (P : Ideal (𝓞 D.host.E)) (s : 𝓞 D.host.E)
    (h : Formalism.L2.Col.cO D.host.E s ∈ P) : s ∈ conjI P :=
  Ideal.subset_span ⟨_, h, (cc_star D (s : D.host.E)).symm⟩

theorem exists_int_inv_half : ∀ (D : D7) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P →
    ∀ s : 𝓞 D.host.E, (∀ PP ∈ P, s ∉ conjI PP.asIdeal) →
    ∃ t : AE D, finPart D t ∈ intAE D ∧ t * incA D (s : D.host.E) * cA D e = cA D e := by
  intro D P e he s hs
  have hee : e * e = e := GlobalTheory.PlaceVec.idemSum_mul_self he
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  by_cases hP : P = ∅
  · subst hP
    refine ⟨0, by rw [map_zero]; exact zero_mem _, ?_⟩
    simp
  obtain ⟨tableDegreeThreeBase, hPP0⟩ := Finset.nonempty_iff_ne_empty.2 hP
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hs tableDegreeThreeBase hPP0 (zero_mem _)
  have hsE : (s : D.host.E) ≠ 0 := by
    intro h; apply hs0; exact RingOfIntegers.ext (by simpa using h)
  refine ⟨cA D (∑ PP ∈ P, es PP) * incA D ((s : D.host.E)⁻¹), ?_, ?_⟩
  · rw [map_sum, Finset.sum_mul, map_sum]
    refine sum_mem fun PP hPP => ?_
    have hc0 : Formalism.L2.Col.cO D.host.E s ≠ 0 := by
      intro h0; apply hs0
      rw [← Formalism.L2.Col.cO_cO s, h0, map_zero]
    have hnot : Formalism.L2.Col.cO D.host.E s ∉ PP.asIdeal := fun hm => hs PP hPP (mem_conjI_of D _ s hm)
    have hint := not_not.1 (mt ((hes PP hPP).2 _ hc0).2 hnot)
    have := GlobalTheory.MovedIdem.finPart_conj_mem hint
    have hst : star (((Formalism.L2.Col.cO D.host.E s : 𝓞 D.host.E) : D.host.E)⁻¹) = (s : D.host.E)⁻¹ := by
      rw [star_inv₀]
      congr 1
      exact star_star (s : D.host.E)
    rwa [hst] at this
  · have h1 : incA D ((s : D.host.E)⁻¹) * incA D (s : D.host.E) = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hsE, map_one]
    calc cA D (∑ PP ∈ P, es PP) * incA D ((s : D.host.E)⁻¹) * incA D (s : D.host.E) * cA D (∑ PP ∈ P, es PP)
        = cA D ((∑ PP ∈ P, es PP) * (∑ PP ∈ P, es PP)) := by
          rw [mul_assoc (cA D _), h1, mul_one, map_mul]
      _ = cA D (∑ PP ∈ P, es PP) := by rw [hee]

end GlobalTheory.HalfUnit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteEmbeddingIdempotentPatchInFrameStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteEmbedding_idempotent_patch_in_frame : ∀ {D : D7} (T : HSp D) (βT : GL (Fin T.rank) (EAf D)) (g k : GA D T) (ε : AE D), Formalism.L2.Theta.mt T k = ε • Formalism.L2.Theta.mt T g + (1 - ε) • (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D)) → (Formalism.IndefR.Lev.finE T k : GL (Fin T.rank) (EAf D)).1 = βT.1 * (toEAf D ε • (βT⁻¹ * Formalism.IndefR.Lev.finE T g * βT : GL (Fin T.rank) (EAf D)).1 + (1 - toEAf D ε) • (1 : Matrix (Fin T.rank) (Fin T.rank) (EAf D))) * (βT⁻¹ : GL (Fin T.rank) (EAf D)).1 := by
  first | exact @GlobalTheory.FineCut.finE_cut | exact GlobalTheory.FineCut.finE_cut | (intros; apply GlobalTheory.FineCut.finE_cut <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVacuaLocalFactorsStableHeisenbergAwayStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockVacua_localFactors_stable_heisenberg_away : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsStdChar D ψ (-1) → IsInfFam θ → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → (∀ (q : Place D) (w : WO S T), wAt q w = 0 → VacAt ψ θ S T sS sT ΛS ΛT q f → VacAt ψ θ S T sS sT ΛS ΛT q (heisO ψ S T w f)) ∧ ∀ (p : Place D), IsLocal ψ θ S T sS sT ΛS ΛT p f → (∀ w : WO S T, IsLocal ψ θ S T sS sT ΛS ΛT p (heisO ψ S T (wAt p w) f)) ∧ (∀ (c : ℂ) g, IsLocal ψ θ S T sS sT ΛS ΛT p g → IsLocal ψ θ S T sS sT ΛS ΛT p (c • f + g)) ∧ ∀ τ : D.what₂.Tau, p = .inr τ → ∀ z, IsLocal ψ θ S T sS sT ΛS ΛT p (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f) := by
  first | exact @GlobalTheory.PlaceStable.heis_stable | exact GlobalTheory.PlaceStable.heis_stable | (intros; apply GlobalTheory.PlaceStable.heis_stable <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InducedFunctionL2PositiveStatement
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagLeviGroup GlobalTheory.GKModule GlobalTheory.RealInd
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.induced_function_l2_positive : ∀ (n : ℕ) (ε : Fin n → Bool) (D : Datum ε) (f : UJ ε → D.V), f ∈ D.fns → ∀ g, f g ≠ 0 →
    0 < ∫ k : KG ε, ‖f k‖ ^ 2 ∂muK ε := by
  first | exact @GlobalTheory.RealInd.integral_norm_sq_pos_of_ne_zero | exact GlobalTheory.RealInd.integral_norm_sq_pos_of_ne_zero | (intros; apply GlobalTheory.RealInd.integral_norm_sq_pos_of_ne_zero <;> assumption)
end

