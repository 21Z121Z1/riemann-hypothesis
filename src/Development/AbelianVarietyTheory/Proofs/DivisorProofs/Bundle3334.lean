import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3174
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3323
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3251
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3218
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3300
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3307
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3315
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3324
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3325
import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0393
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3304
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3326
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3330

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectedPDivGroupChartCoboundaryTwoCoord
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Katz.CobCoord

variable {p : ℕ} {k : Type} [CommRing k] {d : ℕ} {G : PDivGroup p k}

theorem connectedPDivGroupChart_eval_nilpotent_pair (c : Chart G d) (n : ℕ) {B : Type} [CommRing B] [Algebra k B] {τ : Type} [Finite τ]
    (E : MvPowerSeries τ k →ₐ[k] B) (hE : ∀ t, IsNilpotent (E (X t)))
    (u v : Fin d → MvPowerSeries τ k) (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) (g : G.A n ⊗[k] G.A n →ₐ[k] B)
    (hgu : ∀ i, E (u i) = g (c.x n i ⊗ₜ 1)) (hgv : ∀ i, E (v i) = g (1 ⊗ₜ c.x n i))
    (s : MvPowerSeries (Fin d ⊕ Fin d) k) : E (at2 s u v) = g (c.ev₂ n s) := by
  have hy : ∀ j, IsNilpotent (g (c.x₂ n j)) := fun j => (c.nil₂ n j).map g
  have h1 := (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin d ⊕ Fin d) B).1 τ E hE (Sum.elim u v)
    (by rintro (i | i) <;> simp [hu, hv]) (fun j => g (c.x₂ n j)) hy
    (by rintro (i | i) <;> simp [Chart.x₂, hgu, hgv]) s
  have h2 := (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin d ⊕ Fin d) (G.A n ⊗[k] G.A n)).2 B g (c.x₂ n) (c.nil₂ n)
    (fun j => g (c.x₂ n j)) hy (fun _ => rfl) s
  unfold at2
  rw [h1, Chart.ev₂, h2]

end GlobalTheory.Katz.CobCoord

namespace GlobalTheory.Katz.CobCoord

variable (k : Type) [CommRing k] (A : Type) [CommRing A] [Bialgebra k A]

abbrev gSumL : A ⊗[k] A →ₐ[k] A ⊗[k] (A ⊗[k] A) :=
  (Algebra.TensorProduct.assoc k k k A A A).toAlgHom.comp
    (Algebra.TensorProduct.map (Bialgebra.comulAlgHom k A) (AlgHom.id k A))

abbrev gSumR : A ⊗[k] A →ₐ[k] A ⊗[k] (A ⊗[k] A) :=
  Algebra.TensorProduct.map (AlgHom.id k A) (Bialgebra.comulAlgHom k A)

abbrev gFst : A ⊗[k] A →ₐ[k] A ⊗[k] (A ⊗[k] A) :=
  Algebra.TensorProduct.map (AlgHom.id k A) (Algebra.TensorProduct.includeLeft (S := k))

theorem algAssoc_apply (w : (A ⊗[k] A) ⊗[k] A) :
    Algebra.TensorProduct.assoc k k k A A A w = TensorProduct.assoc k A A A w := by
  induction w with
  | zero => simp
  | tmul x b =>
    induction x with
    | zero => simp
    | tmul a a' => simp
    | add x y hx hy => simp only [add_tmul, map_add, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem gSumL_apply (t : A ⊗[k] A) :
    gSumL k A t = TensorProduct.assoc k A A A (Coalgebra.comul.rTensor A t) := by
  induction t with
  | zero => simp
  | tmul a b => simp [algAssoc_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem gSumR_apply (t : A ⊗[k] A) : gSumR k A t = Coalgebra.comul.lTensor A t := by
  induction t with
  | zero => simp
  | tmul a b => simp
  | add x y hx hy => simp only [map_add, hx, hy]

theorem gFst_apply (t : A ⊗[k] A) :
    gFst k A t = ((TensorProduct.mk k A A).flip 1).lTensor A t := by
  induction t with
  | zero => simp
  | tmul a b => simp
  | add x y hx hy => simp only [map_add, hx, hy]

theorem gFst_eq_assoc (t : A ⊗[k] A) :
    gFst k A t = Algebra.TensorProduct.assoc k k k A A A (t ⊗ₜ 1) := by
  induction t with
  | zero => simp
  | tmul a b => simp
  | add x y hx hy => simp only [map_add, hx, hy, add_tmul]

theorem cobTwo_eq (t : A ⊗[k] A) : cobTwo k A t =
    Algebra.TensorProduct.includeRight t - gSumL k A t + gSumR k A t - gFst k A t := by
  rw [cobTwo_apply, gSumL_apply, gSumR_apply, gFst_apply, Algebra.TensorProduct.includeRight_apply]

end GlobalTheory.Katz.CobCoord

namespace GlobalTheory.Katz.CobCoord

theorem evA_cob2_eq_cobTwo_and_op_assoc : ∀ (p : ℕ) (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k) (c : Chart G d),
    ∀ (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), c.IsLawOf μ →
    ∀ n (h : ∀ i, IsNilpotent ((Sum.elim (fun i => c.x n i ⊗ₜ[k] (1 : G.A n ⊗[k] G.A n))
      (fun j => (1 : G.A n) ⊗ₜ[k] c.x₂ n j)) i)),
    (∀ s, evA k _ h (cob2 μ s) = cobTwo k (G.A n) (c.ev₂ n s)) ∧
      ∀ i, evA k _ h (op μ (op μ x1 x2) x3 i) = evA k _ h (op μ x1 (op μ x2 x3) i) := by
  intro p k _ d G c μ hμ n h
  have hX := GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate k _ _ _ h
  have hE : ∀ t, IsNilpotent (evA k _ h (X t)) := fun t => by rw [hX]; exact h t
  have hμ0 := ((GlobalTheory.T.connectedPDivGroup_formalLaw_coordinates p k d G c).2 μ hμ).1
  have e1 : ∀ i, evA k _ h (x1 i) = c.x n i ⊗ₜ 1 := fun i => hX (Sum.inl i)
  have e2 : ∀ i, evA k _ h (x2 i) = 1 ⊗ₜ (c.x n i ⊗ₜ 1) := fun i => hX (Sum.inr (Sum.inl i))
  have e3 : ∀ i, evA k _ h (x3 i) = 1 ⊗ₜ (1 ⊗ₜ c.x n i) := fun i => hX (Sum.inr (Sum.inr i))
  have c1 : ∀ i, constantCoeff (x1 i : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k) = 0 :=
    fun _ => constantCoeff_X _
  have c2 : ∀ i, constantCoeff (x2 i : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k) = 0 :=
    fun _ => constantCoeff_X _
  have c3 : ∀ i, constantCoeff (x3 i : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k) = 0 :=
    fun _ => constantCoeff_X _
  have cop : ∀ u v : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k,
      (∀ i, constantCoeff (u i) = 0) → (∀ i, constantCoeff (v i) = 0) →
      ∀ i, constantCoeff (op μ u v i) = 0 := by
    intro u v hu hv i
    have hs : ∀ j, constantCoeff (Sum.elim u v j) = 0 := by rintro (j | j) <;> simp [hu, hv]
    exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hs) hs (hμ0 i)
  have o12 : ∀ i, evA k _ h (op μ x1 x2 i) = gFst k (G.A n) (Coalgebra.comul (c.x n i)) := by
    intro i
    rw [op, connectedPDivGroupChart_eval_nilpotent_pair c n _ hE x1 x2 c1 c2 (gFst k (G.A n)) (fun j => by rw [e1]; simp [Algebra.TensorProduct.one_def])
      (fun j => by rw [e2]; simp [Algebra.TensorProduct.one_def]), hμ n i]
  have o23 : ∀ i, evA k _ h (op μ x2 x3 i) =
      Algebra.TensorProduct.includeRight (Coalgebra.comul (c.x n i)) := by
    intro i
    rw [op, connectedPDivGroupChart_eval_nilpotent_pair c n _ hE x2 x3 c2 c3 Algebra.TensorProduct.includeRight
      (fun j => by rw [e2]; simp [Algebra.TensorProduct.one_def]) (fun j => by rw [e3]; simp [Algebra.TensorProduct.one_def]), hμ n i]
  have a2 := connectedPDivGroupChart_eval_nilpotent_pair c n _ hE (op μ x1 x2) x3 (cop _ _ c1 c2) c3 (gSumL k (G.A n))
    (fun j => by rw [o12, gFst_eq_assoc]; simp)
    (fun j => by rw [e3]; simp [Algebra.TensorProduct.one_def])
  have a3 := connectedPDivGroupChart_eval_nilpotent_pair c n _ hE x1 (op μ x2 x3) c1 (cop _ _ c2 c3) (gSumR k (G.A n))
    (fun j => by rw [e1]; simp [Algebra.TensorProduct.one_def]) (fun j => by rw [o23]; simp)
  refine ⟨fun s => ?_, fun i => ?_⟩
  · have a1 := connectedPDivGroupChart_eval_nilpotent_pair c n _ hE x2 x3 c2 c3 Algebra.TensorProduct.includeRight
      (fun j => by rw [e2]; simp [Algebra.TensorProduct.one_def]) (fun j => by rw [e3]; simp [Algebra.TensorProduct.one_def]) s
    have a4 := connectedPDivGroupChart_eval_nilpotent_pair c n _ hE x1 x2 c1 c2 (gFst k (G.A n))
      (fun j => by rw [e1]; simp [Algebra.TensorProduct.one_def]) (fun j => by rw [e2]; simp [Algebra.TensorProduct.one_def]) s
    rw [cob2, map_sub, map_add, map_sub, a1, a2, a3, a4, cobTwo_eq]
  · change evA k _ h (at2 (μ i) (op μ x1 x2) x3) = evA k _ h (at2 (μ i) x1 (op μ x2 x3))
    rw [a2, a3, hμ n i, gSumL_apply, gSumR_apply, Coalgebra.coassoc_apply]

end GlobalTheory.Katz.CobCoord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectedPDivGroupChartSemilinearHomIsFormalGrou
section
set_option autoImplicit false

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz

theorem isHom_map_of_semiHom_ev (p : ℕ) (k k' : Type) [CommRing k] [CommRing k'] (σ : k →+* k')
    (d e : ℕ) (G : PDivGroup p k) (G' : PDivGroup p k') (c : Chart G d) (c' : Chart G' e)
    (s : SemiHom σ G' G) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k)
    (ν : Fin e → MvPowerSeries (Fin e ⊕ Fin e) k') (φ : Fin d → MvPowerSeries (Fin e) k')
    (hμ : c.IsLawOf μ) (hν : c'.IsLawOf ν) (hφ : ∀ n j, c'.ev n (φ j) = s.app n (c.x n j))
 :
    IsHom ν (fun i => MvPowerSeries.map σ (μ i)) φ := by
  have hL := (GlobalTheory.T.connectedPDivGroup_formalLaw_coordinates p k' e G' c').2 ν hν
  have h2 := GlobalTheory.T.semilinearPDivGroupHom_eval_two_variable_series p k k' σ d e G G' c c' s φ hφ
  refine ⟨fun j => ?_, fun j => ?_⟩
  · have h0 := (GlobalTheory.Katz.counit_dUnit_evA k' e (G'.A 0) (c'.x 0) (c'.nil 0) (c'.aug 0) (φ j)).1
    change Coalgebra.counit (R := k') (c'.ev 0 (φ j)) = _ at h0
    rw [← h0, hφ 0 j, (s.app 0).counit_map, c.aug 0 j, map_zero]
  · let z : ∀ n, G'.A n ⊗[k'] G'.A n := fun n => Coalgebra.comul (R := k') (s.app n (c.x n j))
    have hz : ∀ n, pullbackTwo (G'.res n) (z (n + 1)) = z n := fun n => by
      simp only [z]
      rw [pullTwo_comul, s.res_app, c.res]
    have hl : ∀ n, c'.ev₂ n (subst ν (φ j)) = z n := fun n => by
      rw [(hL.2 n (φ j)).1, hφ n j]
    have hr : ∀ n, c'.ev₂ n (pull2 φ (MvPowerSeries.map σ (μ j))) = z n := fun n => by
      rw [h2 n (μ j), hμ n j, SemiBialgHom.two_comul]
    exact ((GlobalTheory.T.chart_square_coordinates_present_levels p k' e G' c').2 z hz).unique hl hr

end GlobalTheory.Katz
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotangentKernelEqCokerOmegaMapStatement
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cotangent_kernel_eq_coker_omegaMap : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (G H : PDivGroup p k) (q : G ⟶ H) (C : Type) [CommRing C] [HopfAlgebra k C] [IsCocomm k C] [Module.Finite k C] (π : G.A 1 →ₐc[k] C), Function.Surjective π → (kerIdeal (q.app 1) ≤ RingHom.ker π → ∀ w ∈ LinearMap.range (omegaMap G H q), cotMap π (w.1 1) = 0) ∧ (RingHom.ker π ≤ kerIdeal (q.app 1) ⊔ augIdeal k (G.A 1) ^ 2 → kerIdeal (q.app 1) ≤ RingHom.ker π → Module.finrank k (G.omega ⧸ LinearMap.range (omegaMap G H q)) = Module.finrank k (Cot k C)) ∧ ∀ (H' : PDivGroup p k) (f : G ⟶ H'), (∀ w ∈ LinearMap.range (omegaMap G H' f), cotMap π (w.1 1) = 0) → cotMap (π.comp (f.app 1)) = 0 := by
  first | exact @GlobalTheory.PDivGroup.cot_kernel_eq_coker_omegaMap | exact GlobalTheory.PDivGroup.cot_kernel_eq_coker_omegaMap | (intros; apply GlobalTheory.PDivGroup.cot_kernel_eq_coker_omegaMap <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormsExtendVanishCompactifiedFlagSpaceStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForms_extend_vanish_compactifiedFlagSpace : ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂) (la : AllWt.Weight (T.Q.Dw j)), Extends TF.X Z Y.U la := by
  first | exact @GlobalTheory.CompHS.cusp_extends_comp | exact GlobalTheory.CompHS.cusp_extends_comp | (intros; apply GlobalTheory.CompHS.cusp_extends_comp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneBaseChangeBasisStatement
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dieudonne_baseChange_basis : ∀ (p : ℕ) [Fact p.Prime] (P : ∀ (k : Type) [CommRing k], PDivGroup p k → Prop) (B : Base p P) (k k' : Type) [Field k] [CharP k p] [PerfectRing k p] [Field k'] [CharP k' p] [PerfectRing k' p] [Algebra k k'] (G : PDivGroup p k) (hG : P k G) (hG' : P k' (G.baseChange k')) (ι : Type) [Fintype ι] (b : Module.Basis ι (WittVector p k) (B.M G hG)), ∃ b' : Module.Basis ι (WittVector p k') (B.M (G.baseChange k') hG'), ∀ i, b' i = B.smap hG' hG (G.toBase k') (b i) := by
  first | exact @GlobalTheory.Dieu.Base.smap_toBase_basis | exact GlobalTheory.Dieu.Base.smap_toBase_basis | (intros; apply GlobalTheory.Dieu.Base.smap_toBase_basis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneFunctorBaseFunctorPropertiesStatement
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dieudonneFunctorBase_functor_properties : ∀ (p : ℕ) [Fact p.Prime] (P : ∀ (k : Type) [CommRing k], PDivGroup p k → Prop) (B : Base p P) (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G H K : PDivGroup p k) (hG : P k G) (hH : P k H) (hK : P k K), B.map hG hG (𝟙 G) = LinearMap.id ∧ (∀ (f : G ⟶ H) (g : H ⟶ K), B.map hG hK (f ≫ g) = B.map hG hH f ∘ₗ B.map hH hK g) ∧ (∀ f g : G ⟶ H, B.map hG hH (f + g) = B.map hG hH f + B.map hG hH g) ∧ B.map hG hH (0 : G ⟶ H) = 0 ∧ (∀ (n : ℕ) (f : G ⟶ H) (m : B.M H hH), B.map hG hH ((p : ℤ_[p]) ^ n • f) m = p ^ n • B.map hG hH f m) ∧ (∀ (f : G ⟶ H) (m : B.M H hH), B.red G hG (B.map hG hH f m) = rigExtMap f (B.red H hH m)) ∧ (∀ (f : G ⟶ H) (m : B.M H hH), B.map hG hH f (B.F H hH m) = B.F G hG (B.map hG hH f m)) ∧ Module.finrank (WittVector p k) (B.M G hG) = G.height ∧ ∀ (n : ℕ) (m : B.M G hG), p ^ n • m = 0 → m = 0 := by
  first | exact @GlobalTheory.Dieu.base_functor_props | exact GlobalTheory.Dieu.base_functor_props | (intros; apply GlobalTheory.Dieu.base_functor_props <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8ThetaSetupGenericPointExistsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_e8_setup_over_generic_point : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z), IsProjOver z → IsNormalScheme Z → IsOpenImmersion i → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ThetaInt F W i → ∀ η ∈ genericPoints F.X, ∀ B : ℕ, ∃ X₁ : Setup F W i, B ≤ X₁.S.N ∧ ∀ w, (spMap X₁.S.R.val.toRingHom ≫ X₁.u) w = η := by
  first | exact @GlobalTheory.Poinc.GSetup.exists_setup | exact GlobalTheory.Poinc.GSetup.exists_setup | (intros; apply GlobalTheory.Poinc.GSetup.exists_setup <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqCounitOfHeightOneCotangentPullbackZeroStatement
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_counit_of_heightOne_cotangentPullback_zero : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (C : Type) [CommRing C] [HopfAlgebra k C] [IsCocomm k C] [Module.Finite k C] (D : Type) [CommRing D] [HopfAlgebra k D] [IsCocomm k D] [Module.Finite k D] (f : D →ₐc[k] C), (∀ a ∈ augIdeal k C, a ^ p = 0) → cotMap f = 0 → ∀ d, f d = algebraMap k C (counit (R := k) d) := by
  first | exact @GlobalTheory.HeightOneHom.eq_algebraMap_counit_of_cotMap_eq_zero | exact GlobalTheory.HeightOneHom.eq_algebraMap_counit_of_cotMap_eq_zero | (intros; apply GlobalTheory.HeightOneHom.eq_algebraMap_counit_of_cotMap_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfFormalGroupLawCoboundaryOneEqZero
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz

theorem eq_zero_of_cob1_eq_zero : ∀ (p : ℕ) (k : Type) [CommRing k] (h : (p : k) = 0) (d : ℕ)
    (G : PDivGroup p k) (c : Chart G d) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k),
    c.IsLawOf μ → ∀ b, cob1 μ b = 0 → b = 0 := by
  intro p k _ h d G c μ hμ b hb
  obtain ⟨hres, -, huniq⟩ := GlobalTheory.T.functions_eq_series_in_chart p k d G c
  have hlaw := ((GlobalTheory.T.connectedPDivGroup_formalLaw_coordinates p k d G c).2 μ hμ).2
  let B : G.funs := ⟨fun n => c.ev n b, fun n => hres n b⟩
  have hB : G.cob B = 0 := by
    refine Subtype.ext (funext fun n => ?_)
    change cobOne k (G.A n) (c.ev n b) = 0
    rw [← (hlaw n b).2, hb, map_zero]
  have hB0 := G.eq_zero_of_cob_eq_zero h hB
  have hb0 : ∀ n, c.ev n b = 0 := fun n => congrArg (fun B : G.funs => B.1 n) hB0
  obtain ⟨f, -, hf⟩ := huniq (fun _ => 0) (fun n => map_zero _)
  exact (hf b hb0).trans (hf 0 fun n => map_zero _).symm

end GlobalTheory.Katz
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleDieudonneTransposeAbsFrobeniusApplyF
section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.Dieu.EtFromConn

namespace GlobalTheory.Dieu.EtFromConn

theorem isTr_absFrob_F : ∀ (p : ℕ) [Fact p.Prime] (B : Base p (fun _ _ G => G.IsConn)) (k : Type)
    [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k) (h : G.IsEt) (l l' : Mod B G h),
    IsTr B (frobRing (p_eq_zero p k)) h h (absFrob (p_eq_zero p k) G) l l' →
      ∀ y, l' (B.F G.dual (dual_conn h) y) = p * WittVector.frobenius (l y) := by
  intro p _ B k _ _ _ G h l l' hT y
  set hp := p_eq_zero p k
  letI : Algebra k k := (frobRing hp).toAlgebra
  obtain ⟨hb, lb, h1, h2⟩ := hT
  have hd := dual_conn h

  have eV : (PerfdLat.dualBaseChange k G).inv ≫ dualHom G (G.baseChange k)
      (absFrob hp G).lift = verschiebung hp G.dual := by
    have := dualHom_relFrob hp G
    change (frobTwistDual hp G).inv ≫ dualHom G _ (relFrob hp G) = _
    rw [← this, Iso.inv_hom_id_assoc]

  have eF : B.F G.dual hd y = B.map hd hb (relFrob hp G.dual)
      (B.smap hb hd (G.dual.toBase k) y) := by
    change B.smap hd hd (absFrob hp G.dual) y = B.smap hd hb (SemiHom.ofHom (relFrob hp G.dual))
      (B.smap hb hd (frobProj hp G.dual) y)
    exact B.smap_comp hd hb hd (frobProj hp G.dual) (SemiHom.ofHom (relFrob hp G.dual))
      (absFrob hp G.dual) (fun n a => by
        change (absFrob hp G.dual).app n a = (relFrob hp G.dual).app n ((frobProj hp G.dual).app n a)
        exact ((relFrob_app_frobProj hp n a).trans (absFrob_app hp G.dual n a).symm).symm) y
  have P := base_functor_props p _ B k (frobTwist hp G.dual) G.dual (frobTwist hp G.dual) hb hd hb
  have P' := base_functor_props p _ B k (frobTwist hp G.dual) (frobTwist hp G.dual)
    (frobTwist hp G.dual) hb hb hb
  have ep : B.map hb hd (verschiebung hp G.dual) (B.map hd hb (relFrob hp G.dual)
      (B.smap hb hd (G.dual.toBase k) y)) = p ^ 1 • B.smap hb hd (G.dual.toBase k) y := by
    set x := B.smap hb hd (G.dual.toBase k) y
    have c := P.2.1 (verschiebung hp G.dual) (relFrob hp G.dual)
    rw [verschiebung_comp_relFrob] at c
    have c2 := LinearMap.congr_fun c x
    calc B.map hb hd (verschiebung hp G.dual) (B.map hd hb (relFrob hp G.dual) x)
        = B.map hb hb ((p : ℤ_[p]) • 𝟙 _) x := c2.symm
      _ = p ^ 1 • B.map hb hb (𝟙 (frobTwist hp G.dual)) x := by
          have e := P'.2.2.2.2.1 1 (𝟙 (frobTwist hp G.dual)) x
          simp only [pow_one] at e ⊢
          exact e
      _ = p ^ 1 • x := congrArg _ (LinearMap.congr_fun P'.1 x)
  rw [h2, eV, eF, ep, map_nsmul, h1, nsmul_eq_mul, pow_one]
  congr 1
  rw [WittVector.frobenius_eq_map_frobenius]
  congr 2
  exact RingHom.ext fun r => frobRing_apply hp r

end GlobalTheory.Dieu.EtFromConn
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleDieudonneTransposeEqRigidifiedExtensionPull
section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.Dieu.EtFromConn

namespace GlobalTheory.Dieu.EtFromConn

theorem rigToLie_toBase_rig {p : ℕ} [Fact p.Prime] {k k' : Type} [Field k] [CharP k p] [Field k']
    [CharP k' p] [Algebra k k'] (G : PDivGroup p k) (r : G.RigExt) (w : G.dual.omega) :
    (G.baseChange k').rigToLie (p_eq_zero p k') ((G.toBase k').rig r)
      (omegaMap _ _ (PerfdLat.dualBaseChange k' G).hom ((G.dual.toBase k').omega w)) =
      algebraMap k k' (G.rigToLie (p_eq_zero p k) r w) := by
  rw [rigToLie_apply, rigToLie_apply, SemiHom.rigToExt_rig,
    SemiHom.extChar_vecExt _ (p_eq_zero p k)]
  exact primLie_toBase G _ w

theorem linearMap_eq_of_liftSemi_surjective {R R' M N : Type} [CommRing R] [CommRing R']
    [Algebra R R'] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R' N]
    (f : M →ₛₗ[algebraMap R R'] N) (hf : Function.Surjective (liftSemi f)) (F₁ F₂ : N →ₗ[R'] R')
    (h : ∀ m, F₁ (f m) = F₂ (f m)) : F₁ = F₂ := by
  refine LinearMap.ext fun v => ?_
  obtain ⟨t, rfl⟩ := hf v
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul r m => rw [liftSemi_tmul, map_smul, map_smul, h]

set_option maxHeartbeats 2000000 in
theorem red_of_isTr (p : ℕ) [Fact p.Prime] (B : Base p (fun _ _ G => G.IsConn)) (k k' : Type)
    [Field k] [CharP k p] [PerfectRing k p] [Field k'] [CharP k' p] [PerfectRing k' p]
    (σ : k →+* k') (G' : PDivGroup p k') (G : PDivGroup p k) (h' : G'.IsEt) (h : G.IsEt)
    (s : SemiHom σ G' G) (l : Mod B G h) (l' : Mod B G' h') (hT : IsTr B σ h' h s l l') :
    red B G' h' l' = s.rig (red B G h l) := by
  letI : Algebra k k' := σ.toAlgebra
  obtain ⟨hb, lb, h1, h2⟩ := hT
  haveI := B.free _ hb
  haveI := B.finite _ hb
  obtain ⟨r', hr', -, -⟩ := wittDual_reduction p k' _ _ (B.red _ hb) (B.red_surjective _ hb)
    (B.red_eq_zero _ hb)
  have hψ : ∀ m, r' lb (B.red _ hb m) = WittVector.constantCoeff (lb m) := hr' lb
  have key1 : ∀ w : G.dual.omega,
      r' lb ((G.dual.baseChange k').rigOfOmega ((G.dual.toBase k').omega w)) =
        σ (G.rigToLie (p_eq_zero p k) (red B G h l) w) := by
    intro w
    obtain ⟨x, hx⟩ := B.red_surjective _ (dual_conn h) (G.dual.rigOfOmega w)
    have e1 : (G.dual.baseChange k').rigOfOmega ((G.dual.toBase k').omega w) =
        B.red _ hb (B.smap hb (dual_conn h) (G.dual.toBase k') x) := by
      rw [B.red_smap, hx, SemiHom.rig_rigOfOmega]
    have e2 : G.rigToLie (p_eq_zero p k) (red B G h l) w = WittVector.constantCoeff (l x) := by
      rw [rigToLie_red, LinearMap.dualMap_apply, ← hx]
      exact (redDual_spec B G h).1 l x
    have e3 : WittVector.constantCoeff (WittVector.map σ (l x)) = σ (WittVector.constantCoeff (l x)) := by
      simp [WittVector.constantCoeff_apply, WittVector.map_coeff]
    exact (congrArg (r' lb) e1).trans ((hψ _).trans ((congrArg _ (h1 x)).trans (e3.trans (congrArg σ e2.symm))))
  have key2 : ((G.baseChange k').rigToLie (p_eq_zero p k') ((G.toBase k').rig (red B G h l))).comp
      (omegaMap _ _ (PerfdLat.dualBaseChange k' G).hom) =
      (r' lb).comp (G.dual.baseChange k').rigOfOmega :=
    linearMap_eq_of_liftSemi_surjective (G.dual.toBase k').omega
      (T.omega_baseChange_bijective_of_p_eq_zero G.dual k' (p_eq_zero p k)).2 _ _ fun w => by
        rw [LinearMap.comp_apply, LinearMap.comp_apply, rigToLie_toBase_rig, key1]
        rfl
  have hinj := (PDivGroup.rigToLie_bijective_and_dual_rigOfOmega_bijective_of_isEt p k'
    (p_eq_zero p k') G' h').1.1
  apply hinj
  rw [rigToLie_red]
  refine LinearMap.ext fun w' => ?_
  rw [LinearMap.dualMap_apply]
  obtain ⟨x', hx'⟩ := B.red_surjective _ (dual_conn h') (G'.dual.rigOfOmega w')
  have hs : ∀ n a, s.app n a = (SemiHom.ofHom s.lift).app n ((G.toBase k').app n a) := fun n a => by
    rw [SemiHom.ofHom_app, toBase_app, SemiHom.lift_app, one_smul]
  have e4 : B.red _ hb (B.map hb (dual_conn h')
      ((PerfdLat.dualBaseChange k' G).inv ≫ dualHom G' (G.baseChange k') s.lift) x') =
      (G.dual.baseChange k').rigOfOmega (omegaMap _ _ (PerfdLat.dualBaseChange k' G).inv
        (omegaMap _ _ (dualHom G' (G.baseChange k') s.lift) w')) := by
    change B.red _ hb (B.smap hb (dual_conn h') (SemiHom.ofHom _) x') = _
    rw [B.red_smap, hx', SemiHom.rig_rigOfOmega, SemiHom.ofHom_omega, omegaMap_comp,
      LinearMap.comp_apply]
  have e5 : G'.rigToLie (p_eq_zero p k') (s.rig (red B G h l)) w' =
      (G.baseChange k').rigToLie (p_eq_zero p k') ((G.toBase k').rig (red B G h l))
        (omegaMap _ _ (dualHom G' (G.baseChange k') s.lift) w') := by
    rw [← (G.toBase k').rig_rig (SemiHom.ofHom s.lift) s hs, SemiHom.ofHom_rig,
      rigToLie_rigExtMap, lieMap_apply]
  have e6 : ∀ v, omegaMap _ _ (PerfdLat.dualBaseChange k' G).hom
      (omegaMap _ _ (PerfdLat.dualBaseChange k' G).inv v) = v := fun v => by
    rw [← LinearMap.comp_apply, ← omegaMap_comp, Iso.hom_inv_id, omegaMap_id, LinearMap.id_apply]
  rw [← hx', (redDual_spec B G' h').1, h2, ← hψ, e4, e5]
  have e7 := LinearMap.congr_fun key2 (omegaMap _ _ (PerfdLat.dualBaseChange k' G).inv
    (omegaMap _ _ (dualHom G' (G.baseChange k') s.lift) w'))
  rw [LinearMap.comp_apply, LinearMap.comp_apply, e6] at e7
  exact e7.symm

end GlobalTheory.Dieu.EtFromConn
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleDieudonneTransposeOfHomEqCompDualHom
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.Dieu.EtFromConn

namespace GlobalTheory.Dieu.EtFromConn

theorem isTr_ofHom : ∀ (p : ℕ) [Fact p.Prime] (B : Base p (fun _ _ G => G.IsConn)) (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G H : PDivGroup p k) (hG : G.IsEt) (hH : H.IsEt) (f : G ⟶ H) (l : Mod B H hH), IsTr B (RingHom.id k) hG hH (SemiHom.ofHom f) l (l ∘ₗ B.map (dual_conn hH) (dual_conn hG) (dualHom G H f)) := by
  intro p _ B k _ _ _ G H hG hH f l
  unfold IsTr
  letI : Algebra k k := (RingHom.id k).toAlgebra
  have hd := dual_conn hH
  have hd' := dual_conn hG
  have hb : (H.dual.baseChange k).IsConn := (baseChange_isConn_isEt p k k H.dual).1 hd
  let φ : H.dual ⟶ H.dual.baseChange k := SemiHom.lift (SemiHom.ofHom (𝟙 H.dual))
  have hφ : ∀ x, B.smap hd hb (SemiHom.ofHom φ) (B.smap hb hd (H.dual.toBase k) x) = x := by
    intro x
    rw [← B.smap_comp hd hb hd (H.dual.toBase k) (SemiHom.ofHom φ) (SemiHom.ofHom (𝟙 _)), B.smap_id]
    intro n a
    exact ((SemiHom.lift_app _ n 1 a).trans (one_smul _ _)).symm
  refine ⟨hb, l ∘ₗ B.map hd hb φ, fun x => ?_, fun y => ?_⟩
  · change l (B.smap hd hb (SemiHom.ofHom φ) (B.smap hb hd (H.dual.toBase k) x)) = _
    rw [hφ, WittVector.map_id, RingHom.id_apply]
  · have hc : ∀ n a, (SemiHom.ofHom ((PerfdLat.dualBaseChange k H).inv ≫
        dualHom G (H.baseChange k) (SemiHom.ofHom f).lift)).app n a =
        (H.dual.toBase k).app n ((SemiHom.ofHom (dualHom G H f)).app n a) := by
      intro n a
      change (CartierDual.baseChange k k (H.A n)).symm (CartierDual.map ((SemiHom.ofHom f).lift.app n) a) = (1 : k) ⊗ₜ CartierDual.map (f.app n) a
      apply EquivLike.injective (CartierDual.baseChange k k (H.A n))
      rw [BialgEquiv.apply_symm_apply]
      refine WithConv.ext (TensorProduct.AlgebraTensorModule.ext fun b m => ?_)
      simp
      rw [SemiHom.lift_app, SemiHom.ofHom_app, map_smul, smul_eq_mul, mul_comm]
    have key := B.smap_comp hb hd hd' (SemiHom.ofHom (dualHom G H f)) (H.dual.toBase k) _ hc y
    change l (B.map hd hd' (dualHom G H f) y) = l (B.smap hd hb (SemiHom.ofHom φ) (B.smap hb hd' _ y))
    rw [key, hφ]
    rfl

end GlobalTheory.Dieu.EtFromConn
end

