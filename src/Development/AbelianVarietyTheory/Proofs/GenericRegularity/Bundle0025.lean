import Mathlib
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsFlagCellChartOverFramedAffineOpen
import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.RegularCharts.MatrixTwoByTwoCongr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsFractionField
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0017
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0015
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0023
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0024
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0021
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0022

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsFlagCellChartOverFramedAffineOpenStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_flagCellChart_over_framedAffineOpen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), FrBC Xo c → ∀ (h : GenFrEx Xo c) (A : Type) [CommRing A] [IsDomain A] [Algebra c.F A] (j : Sp A ⟶ Xo.XF c) (yA : FrPt Xo c A), IsOpenImmersion j → j ≫ pullback.snd _ _ = spMap (algebraMap c.F A) → Algebra.Smooth c.F A → yA.x = j ≫ pullback.fst _ _ → ∀ σ : ∀ τ : E →+* ℂ, Equiv.Perm (Fin (Dw.mult τ)), ∃ C : FChart h, ∀ (L : Type) [Field L] [Algebra c.F L] (f : A →ₐ[c.F] L) (z₀ y : FrPt Xo c L) (x : FlagVar Dw → L) (b : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) L), FrMap f yA z₀ → (∀ τ, (b τ).BlockTriangular id ∧ ∀ i, b τ i i ≠ 0) → Reframe (fun τ => (lowM x τ).submatrix (σ τ).symm id * b τ) z₀ y → ∃ (ψ : C.R →ₐ[c.F] L) (z : FrPt Xo c L) (t' : Ix Dw → Lˣ), FrMap ψ C.y z ∧ FrBor t' z y := by
  first | exact @GlobalTheory.Reg.exists_fChart_cell | exact GlobalTheory.Reg.exists_fChart_cell | (intros; apply GlobalTheory.Reg.exists_fChart_cell <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsFlagCellChartOverModelChart
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.Reg.CellChart

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {M : MChart Y}

theorem lift_point_unique {R : Type} [CommRing R] [Algebra c.F R] {f : Γ(Y.X, M.U) →+* R} {x x' : Sp R ⟶ Xo.X}
    (Λ : M.Lift f x) (Λ' : M.Lift f x') : x = x' := by
  haveI := Y.jQ_open
  have h : Λ.xF = Λ'.xF := by
    rw [← cancel_mono Y.jQ]
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc]
      exact Λ.xF_j.trans Λ'.xF_j.symm
    · rw [Category.assoc, Category.assoc, Y.jQ_over]
      exact Λ.xF_snd.trans Λ'.xF_snd.symm
  rw [← Λ.xF_fst, h, Λ'.xF_fst]

theorem tie_unique {L : Type} [Field L] [Algebra c.F L] {f : Γ(Y.X, M.U) →+* L}
    {u : ∀ τ : E →+* ℂ, Matrix (Fin M.n) (Fin (Dw.mult τ)) L} {y z : FrPt Xo c L} (hy : M.Comparison₂ f u y)
    (hz : M.Comparison₂ f u z) : y = z :=
  GlobalTheory.Reg.TieUniq.frPt_eq_of_tie E H Dw l Xo c O β Y M L f u y z hy hz (lift_point_unique hy.choose hz.choose)

theorem tie_congr {R : Type} [CommRing R] [Algebra c.F R] {f f' : Γ(Y.X, M.U) →+* R}
    {u u' : ∀ τ : E →+* ℂ, Matrix (Fin M.n) (Fin (Dw.mult τ)) R} {y : FrPt Xo c R} (hy : M.Comparison₂ f u y)
    (hf : ∀ a, f a = f' a) (hu : ∀ τ i j, u τ i j = u' τ i j) : M.Comparison₂ f' u' y := by
  obtain rfl : f = f' := RingHom.ext hf
  obtain rfl : u = u' := funext fun τ => Matrix.ext (hu τ)
  exact hy

end

theorem mul_eq_smul_iff_cols {R : Type} [CommRing R] {n r : ℕ} (P : Matrix (Fin n) (Fin n) R) (N : R)
    (u : Matrix (Fin n) (Fin r) R) : P * u = N • u ↔ ∀ i, P.mulVec (fun j => u j i) = N • fun j => u j i :=
  ⟨fun h i => funext fun j => congrFun (congrFun h j) i, fun h => Matrix.ext fun j i => congrFun (h i) j⟩

end GlobalTheory.Reg.CellChart

namespace GlobalTheory.Reg

open GlobalTheory.Reg.CellChart in

theorem exists_pChart_of_cell : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), FrBC Xo c → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O c.F] [IsFractionRing O c.F] (Y : Model Xo c (algebraMap O c.F)), PushInvertible Y.t.G Y.t.PP.L → ∀ (M : MChart Y) (ix : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) ↪ Fin M.n), ∃ (J : Type) (_ : Finite J) (P : J → PChart Xo c (algebraMap O c.F)), ∀ (L : Type) [Field L] [Algebra c.F L] (W : ValuationSubring L) (f : Γ(Y.X, M.U) →+* L) (y : FrPt Xo c L) (Λ : M.Lift f y.x) (u : ∀ τ : E →+* ℂ, Matrix (Fin M.n) (Fin (Dw.mult τ)) L) (b : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) L), (∀ a, f a ∈ W) → (∀ τ i j, u τ i j ∈ W) → (∀ τ, InCell (ix τ) (u τ)) → (∀ τ, (b τ).BlockTriangular id ∧ ∀ i, b τ i i ≠ 0) → Λ.LieTie (fun τ => u τ * b τ) y.u → ∃ j, (P j).Catches W y := by
  intro hS E _ _ _ H Dw l Xo c hbc O _ _ _ _ _ Y hpush M ix
  haveI := M.dom
  obtain ⟨α, es, -, hft, hinj, hne, hes, hop, hpt⟩ := GlobalTheory.Reg.ChartOpens.moduli_basicOpens E H Dw l Xo c O Y M
  obtain ⟨ρ, hρ⟩ := GlobalTheory.Reg.MChart.exists_ringHom_rho E H Dw l Xo c O _ Y M
  have hemb : Function.Injective (embF (E := E) c) := fun τ τ' h =>
    RingHom.ext fun a => congrArg Subtype.val (RingHom.congr_fun h a)
  choose N p hN hp using exists_projector E c.F (embF c) hemb O Γ(Y.X, M.U) α M.n ρ
  have heig : ∀ (R : Type) [CommRing R] [Algebra c.F R] (f : Γ(Y.X, M.U) →+* R),
      f.comp α = (algebraMap c.F R).comp (algebraMap O c.F) → ∀ τ x,
        M.Eig f τ x ↔ ((p τ).map f).mulVec x = f (α (N τ)) • x := by
    intro R _ _ f hf τ x
    rw [← (hp τ R f hf).2 x]
    simp only [hρ]
    rfl
  have hfN : ∀ (L : Type) [Field L] [Algebra c.F L] (f : Γ(Y.X, M.U) →+* L),
      f.comp α = (algebraMap c.F L).comp (algebraMap O c.F) → ∀ τ, f (α (N τ)) ≠ 0 := by
    intro L _ _ f hf τ
    rw [show f (α (N τ)) = algebraMap c.F L (algebraMap O c.F (N τ)) from RingHom.congr_fun hf _]
    exact (map_ne_zero _).mpr ((map_ne_zero_iff _ (IsFractionRing.injective O c.F)).mpr (hN τ))
  have hlift : ∀ e ∈ es, ∀ (R : Type) [CommRing R] [Algebra c.F R] (f : Γ(Y.X, M.U) →+* R),
      f.comp α = (algebraMap c.F R).comp (algebraMap O c.F) → IsUnit (f e) → ∃ x, Nonempty (M.Lift f x) := by
    intro e he R _ _ f hf hu
    obtain ⟨xF, h1, h2⟩ := (hop e he R f hf hu).1
    exact ⟨_, MChart.nonempty_lift E H Dw l Xo c O _ Y M R f xF h1 h2⟩
  have hrk : ∀ (L : Type) [Field L] [Algebra c.F L] (f : Γ(Y.X, M.U) →+* L),
      f.comp α = (algebraMap c.F L).comp (algebraMap O c.F) →
      ∀ e ∈ es, f e ≠ 0 → ∀ τ, ((p τ).map f).rank = Dw.mult τ := by
    intro L _ _ f hf e he hfe τ
    obtain ⟨x, ⟨Λ⟩⟩ := hlift e he L f hf hfe.isUnit
    let S : Submodule L (Fin M.n → L) := Module.End.eigenspace ((p τ).map f).mulVecLin (f (α (N τ)))
    have hS' : ∀ y, y ∈ S ↔ ((p τ).map f).mulVec y = f (α (N τ)) • y := fun y => Module.End.mem_eigenspace_iff
    rw [rank_of_quasi_idem _ _ (hfN L f hf τ) (hp τ L f hf).1 S hS']
    exact GlobalTheory.Reg.finrank_chart_eig E H Dw l Xo c O _ Y M L f x Λ τ S fun y => (hS' y).trans (heig L f hf τ y).symm
  have hpoint : ∀ (L : Type) [Field L] [Algebra c.F L] (f : Γ(Y.X, M.U) →+* L) (y : FrPt Xo c L)
      (Λ : M.Lift f y.x) (u : ∀ τ : E →+* ℂ, Matrix (Fin M.n) (Fin (Dw.mult τ)) L)
      (b : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) L),
      (∀ τ, (b τ).BlockTriangular id ∧ ∀ i, b τ i i ≠ 0) → Λ.LieTie (fun τ => u τ * b τ) y.u →
      f.comp α = (algebraMap c.F L).comp (algebraMap O c.F) ∧ (∃ e ∈ es, f e ≠ 0) ∧
        ∀ τ, (p τ).map f * u τ = f (α (N τ)) • u τ := by
    intro L _ _ f y Λ u b hb ht
    obtain ⟨hf, he⟩ := hpt L f Λ.xF Λ.xF_snd Λ.xF_j
    refine ⟨hf, he, fun τ => ?_⟩
    have h1 : (p τ).map f * (u τ * b τ) = f (α (N τ)) • (u τ * b τ) :=
      (mul_eq_smul_iff_cols _ _ _).mpr fun i => (heig L f hf τ _).mp
        ((GlobalTheory.Reg.isEigAt_iff_eig E H Dw l Xo c O _ Y M L f y.x Λ τ _ _ (ht τ i)).mp (y.eig τ i))
    have hd : IsUnit (b τ).det := by
      rw [Matrix.det_of_upperTriangular (hb τ).1]
      exact (Finset.prod_ne_zero_iff.mpr fun i _ => (hb τ).2 i).isUnit
    have h2 := congrArg (· * (b τ)⁻¹) h1
    simp only [Matrix.mul_assoc, Matrix.smul_mul, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one] at h2
    exact h2
  by_cases hκ : ∃ κ₀ : ∀ τ, Fin (Dw.mult τ) → Fin M.n, ∀ τ, ((p τ).submatrix (ix τ) (κ₀ τ)).det ≠ 0
  swap
  · refine ⟨Empty, inferInstance, Empty.elim, fun L _ _ W f y Λ u b _ _ hc hb ht => (hκ ?_).elim⟩
    obtain ⟨hf, -, hu⟩ := hpoint L f y Λ u b hb ht
    choose κ hκL using fun τ => exists_minor _ _ (hfN L f hf τ) (ix τ) (u τ) (hu τ) (hc τ)
    refine ⟨κ, fun τ h => hκL τ ?_⟩
    have := RingHom.map_det f ((p τ).submatrix (ix τ) (κ τ))
    rw [h, map_zero] at this
    exact this.symm
  obtain ⟨κ₀, hκ₀⟩ := hκ
  obtain ⟨Ω, _, _, gens, es', g, u, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
    exists_cell_algebra c.F O Γ(Y.X, M.U) (E →+* ℂ) α hft hinj es hes hne M.n Dw.mult ix N hN p
      (fun L _ _ f hf τ => (hp τ L f hf).1) hrk (fun e he R _ _ f hf hu => (hop e he R f hf hu).2) κ₀ hκ₀
  choose hsm fe ue k1 k2 k3 k4 k5 k6 using h8
  have hy : ∀ e (he : e ∈ es'), ∃ y : FrPt Xo c (Algebra.adjoin c.F (insert e⁻¹ (gens : Set Ω))),
      M.Comparison₂ (fe e he) (ue e he) y := by
    intro e he
    obtain ⟨e₀, he₀, hu⟩ := k4 e he
    obtain ⟨x, ⟨Λ⟩⟩ := hlift e₀ he₀ _ (fe e he) (k3 e he) hu
    obtain ⟨y, -, hy⟩ := GlobalTheory.Reg.exists_frPt_tie hS E H Dw l Xo c O _ Y M _ (fe e he) x Λ (ue e he)
      (fun τ i => (heig _ _ (k3 e he) τ _).mpr ((mul_eq_smul_iff_cols _ _ _).mp (k5 e he τ) i))
      (fun τ cv h => k6 e he τ cv ((heig _ _ (k3 e he) τ _).mp h))
    exact ⟨y, hy⟩
  choose yy hyy using hy
  have hgen : ∀ e (he : e ∈ es') z, FrMap (Algebra.adjoin c.F (insert e⁻¹ (gens : Set Ω))).val (yy e he) z →
      M.Comparison₂ g u z := fun e he z hz =>
    tie_congr (GlobalTheory.Reg.MChart.tie_baseChange E H Dw l Xo c O _ Y M _ _ _ _ _ _ _ (hyy e he) hz) (k1 e he) (k2 e he)
  obtain ⟨e₁, he₁⟩ := id h2
  obtain ⟨yg, hyg⟩ := hbc _ _ (Algebra.adjoin c.F (insert e₁⁻¹ (gens : Set Ω))).val (yy e₁ he₁)
  have hint : ∀ e (he : e ∈ es') (T : CDVR) (io : c.F →+* T.Fr), letI := io.toAlgebra
      ∀ (ψ : Algebra.adjoin c.F (insert e⁻¹ (gens : Set Ω)) →ₐ[c.F] T.Fr),
        (∀ a : O, io (algebraMap O c.F a) ∈ Set.range (algebraMap T.V T.Fr)) →
        (∀ w : Algebra.adjoin c.F (insert e⁻¹ (gens : Set Ω)), (w : Ω) ∈ gens →
          ψ w ∈ Set.range (algebraMap T.V T.Fr)) →
        ∀ z : FrPt Xo c T.Fr, FrMap ψ (yy e he) z → Integral T io z := by
    intro e he T io
    letI := io.toAlgebra
    intro ψ hO hg z hz
    have hVinj : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective _ _
    have hB : ∀ w ∈ Subring.closure (Set.range ((algebraMap c.F Ω).comp (algebraMap O c.F)) ∪ (gens : Set Ω)),
        w ∈ (((algebraMap T.V T.Fr).range.comap ψ.toRingHom).map
          (Algebra.adjoin c.F (insert e⁻¹ (gens : Set Ω))).val.toRingHom) := by
      intro w hw
      refine (Subring.closure_le.mpr ?_) hw
      rintro w (⟨o, rfl⟩ | hw)
      · refine ⟨algebraMap c.F _ (algebraMap O c.F o), ?_, rfl⟩
        obtain ⟨v, hv⟩ := hO o
        exact ⟨v, hv.trans (ψ.commutes _).symm⟩
      · exact ⟨⟨w, Algebra.subset_adjoin (Or.inr hw)⟩, hg _ hw, rfl⟩
    have hfa : ∀ a, ψ.toRingHom.comp (fe e he) a ∈ (algebraMap T.V T.Fr).range := by
      intro a
      obtain ⟨w, hw, hw'⟩ := hB _ (h4 a)
      obtain rfl : w = fe e he a := Subtype.ext (hw'.trans (k1 e he a).symm)
      exact hw
    let φ := (algebraMap T.V T.Fr).rangeRestrict
    let ε : T.V ≃+* (algebraMap T.V T.Fr).range := RingEquiv.ofBijective φ
      ⟨fun a b h => hVinj (congrArg Subtype.val h), (algebraMap T.V T.Fr).rangeRestrict_surjective⟩
    let f₀ : Γ(Y.X, M.U) →+* T.V := ε.symm.toRingHom.comp ((ψ.toRingHom.comp (fe e he)).codRestrict _ hfa)
    have hf₀ : ∀ a, algebraMap T.V T.Fr (f₀ a) = ψ (fe e he a) := fun a =>
      congrArg Subtype.val (ε.apply_symm_apply ⟨_, hfa a⟩)
    choose u₀ hu₀ using fun τ i j => hg (ue e he τ i j) (by rw [k2]; exact h5 τ i j)
    refine GlobalTheory.Reg.tie_integral hS E H Dw l Xo c O _ Y M hpush T io f₀ ix u₀ (fun τ => ⟨fun i j hij => hVinj ?_,
      fun i => hVinj ?_⟩) z (tie_congr (GlobalTheory.Reg.MChart.tie_baseChange E H Dw l Xo c O _ Y M _ _ _ _ _ _ _ (hyy e he) hz)
        (fun a => (hf₀ a).symm) fun τ i j => (hu₀ τ i j).symm)
    · rw [hu₀, show ue e he τ (ix τ i) j = 0 from Subtype.ext ((k2 e he τ _ _).trans ((h7 τ).1 i j hij)),
        map_zero, map_zero]
    · rw [hu₀, show ue e he τ (ix τ i) i = 1 from Subtype.ext ((k2 e he τ _ _).trans ((h7 τ).2 i)),
        map_one, map_one]
  let P : PChart Xo c (algebraMap O c.F) :=
    { Ω := Ω, gens := gens, frac := h1, es := es', es_ne := h2, es_mem := h3, sm := hsm, yg := yg, y := yy
      gen := fun e he => by
        obtain ⟨z, hz⟩ := hbc _ _ (Algebra.adjoin c.F (insert e⁻¹ (gens : Set Ω))).val (yy e he)
        rw [tie_unique (hgen _ _ _ hyg) (hgen _ _ _ hz)]
        exact hz
      int := hint }
  refine ⟨Unit, inferInstance, fun _ => P, fun L _ _ W f y Λ u' b hW hW' hc hb ht => ⟨(), ?_⟩⟩
  obtain ⟨hf, ⟨e₀, he₀, hfe⟩, hu⟩ := hpoint L f y Λ u' b hb ht
  obtain ⟨e, he, ψ, hψ1, hψ2⟩ := h9 L f hf e₀ he₀ hfe u' hu hc
  obtain ⟨z, hz⟩ := hbc _ _ ψ (yy e he)
  have htz : M.Comparison₂ f u' z := by
    refine tie_congr (GlobalTheory.Reg.MChart.tie_baseChange E H Dw l Xo c O _ Y M _ _ _ _ _ _ _ (hyy e he) hz) (fun a => ?_) fun τ i j => ?_
    · exact (congrArg ψ (Subtype.ext (k1 e he a))).trans (hψ1 a (k1 e he a ▸ (fe e he a).2))
    · exact (congrArg ψ (Subtype.ext (k2 e he τ i j))).trans (hψ2 τ i j (k2 e he τ i j ▸ (ue e he τ i j).2))
  obtain ⟨t, ht'⟩ := GlobalTheory.Reg.frBor_of_tie E H Dw l Xo c O _ Y M L f y z Λ u' b (lift_point_unique htz.choose Λ) hb ht htz
  refine ⟨e, he, ψ, z, t, ?_, hz, ht'⟩
  rintro ⟨w, hw⟩ hwg
  rcases h6 w hwg with ⟨a, rfl⟩ | ⟨τ, i, j, rfl⟩
  · exact (hψ1 a hw).symm ▸ hW a
  · exact (hψ2 τ i j hw).symm ▸ hW' τ i j

end GlobalTheory.Reg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsSectionOfGenericValuesRegularOnCharts
section
noncomputable section

namespace GlobalTheory.Reg.SecGlue

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def liftF {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) : Sp S ⟶ Xo.XF c :=
  pullback.lift y.x (spMap (algebraMap c.F S)) (by
    rw [y.x_over, spMap_comp_ring]; rfl)

theorem liftF_fst {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) :
    liftF y ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) = y.x :=
  pullback.lift_fst _ _ _

theorem liftF_snd {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) :
    liftF y ≫ pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) = spMap (algebraMap c.F S) :=
  pullback.lift_snd _ _ _

theorem liftF_map {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T)
    (y : FrPt Xo c S) (z : FrPt Xo c T) (h : z.x = spMap φ.toRingHom ≫ y.x) :
    liftF z = spMap φ.toRingHom ≫ liftF y := by
  apply pullback.hom_ext
  · rw [Category.assoc, liftF_fst, liftF_fst, h]
  · rw [Category.assoc, liftF_snd, liftF_snd, spMap_comp_ring]
    congr 1
    exact RingHom.ext fun r => (φ.commutes r).symm

theorem liftF_congr {S : Type} [CommRing S] [Algebra c.F S] (y z : FrPt Xo c S) (h : z.x = y.x) :
    liftF z = liftF y := by
  apply pullback.hom_ext
  · rw [liftF_fst, liftF_fst, h]
  · rw [liftF_snd, liftF_snd]

theorem liftF_gen (h : GenFrEx Xo c) (Z : Comp Xo c) :
    liftF (genFr h Z) = spMap (algebraMap (kap Z) (Om Z)) ≫ genSp Z := by
  have e : spMap (algebraMap c.F (kap Z)) = genSp Z ≫ strK := Spec.map_preimage _
  apply pullback.hom_ext
  · rw [liftF_fst, (isGenFr_genFr h Z).1, Category.assoc]; rfl
  · rw [liftF_snd, Category.assoc]
    erw [← e]
    rw [spMap_comp_ring]

theorem liftF_gen_apply (h : GenFrEx Xo c) (Z : Comp Xo c) (p : Sp (Om Z)) :
    liftF (genFr h Z) p = genPt Z := by
  rw [liftF_gen, Scheme.Hom.comp_apply]
  exact Scheme.fromSpecResidueField_apply _ _

theorem closure_gen (Z : Comp Xo c) : closure {genPt Z} = (Z : Set (Xo.XF c)) :=
  ((Z.2.1 : IsIrreducible (Z : Set (Xo.XF c))).isGenericPoint_genericPoint
    (isClosed_of_mem_irreducibleComponents _ Z.2)).def

theorem chart_comp {h : GenFrEx Xo c} (Z : Comp Xo c) (C : FChart h) (ψ : C.R →ₐ[c.F] Om Z)
    (z : FrPt Xo c (Om Z)) (t : Ix Dw → (Om Z)ˣ) (h1 : FrMap ψ C.y z) (h2 : FrBor t z (genFr h Z)) : C.Z = Z := by
  have e1 : liftF (genFr h Z) = spMap ψ.toRingHom ≫ liftF C.y := by
    rw [liftF_congr _ _ h2.1, liftF_map ψ _ _ h1.1]
  have e2 : liftF (genFr h C.Z) = spMap C.R.val.toRingHom ≫ liftF C.y := by
    rw [← liftF_congr _ _ C.bor.1, liftF_map _ _ _ C.gen.1]
  let p : Sp (Om Z) := IsLocalRing.closedPoint (Om Z)
  let p' : Sp (Om C.Z) := IsLocalRing.closedPoint (Om C.Z)
  have f1 := liftF_gen_apply h Z p
  have f2 := liftF_gen_apply h C.Z p'
  rw [e1, Scheme.Hom.comp_apply] at f1
  rw [e2, Scheme.Hom.comp_apply] at f2
  have hs : (spMap C.R.val.toRingHom p' : Sp C.R) ⤳ spMap ψ.toRingHom p := by
    refine (PrimeSpectrum.le_iff_specializes _ _).1 ?_
    intro x hx
    have hx' : (x : Om C.Z) ∈ IsLocalRing.maximalIdeal (Om C.Z) := hx
    rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot] at hx'
    have : x = 0 := Subtype.ext hx'
    rw [this]
    exact Ideal.zero_mem _
  have hs' := hs.map (liftF C.y).continuous
  rw [f1, f2] at hs'
  have hm : genPt Z ∈ (C.Z : Set (Xo.XF c)) := by
    rw [← closure_gen]; exact hs'.mem_closure
  have hsub : (Z : Set (Xo.XF c)) ⊆ C.Z := by
    rw [← closure_gen Z]
    exact closure_minimal (Set.singleton_subset_iff.2 hm) (isClosed_of_mem_irreducibleComponents _ C.Z.2)
  exact Subtype.ext (Set.Subset.antisymm (Z.2.2 C.Z.2.1 hsub) hsub)

theorem wchar_mul {S : Type} [CommRing S] (e : Ix Dw → ℕ) (t t' : Ix Dw → Sˣ) :
    wchar e (t * t') = wchar e t * wchar e t' := by
  simp only [wchar, Pi.mul_apply, Units.val_mul, mul_pow, Finset.prod_mul_distrib]

theorem wchar_one {S : Type} [CommRing S] (e : Ix Dw → ℕ) : wchar e (1 : Ix Dw → Sˣ) = 1 := by
  simp [wchar]

theorem wchar_map {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T)
    (e : Ix Dw → ℕ) (t : Ix Dw → Sˣ) :
    wchar e (fun i => Units.map (φ : S →* T) (t i)) = φ (wchar e t) := by
  simp [wchar]

theorem eq_of_fields {K S : Type} [Field K] [CommRing S] [IsReduced S] [Algebra K S] (s s' : S)
    (hs : ∀ (L : Type) [Field L] [Algebra K L] (χ : S →ₐ[K] L), χ s = χ s') : s = s' := by
  rw [← sub_eq_zero]
  apply IsNilpotent.eq_zero
  rw [nilpotent_iff_mem_prime]
  intro P hP
  have := hs (FractionRing (S ⧸ P))
    ((IsScalarTower.toAlgHom K (S ⧸ P) (FractionRing (S ⧸ P))).comp (Ideal.Quotient.mkₐ K P))
  exact Ideal.Quotient.eq.1 (IsFractionRing.injective (S ⧸ P) (FractionRing (S ⧸ P)) this)

section Val

variable {h : GenFrEx Xo c} {e : Ix Dw → ℕ} {b : ∀ Z : Comp Xo c, Om Z}
  (hb : ∀ C : FChart h, wchar e C.t * b C.Z ∈ C.R)

def Val {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v : S) : Prop :=
  ∃ (C : FChart h) (ψ : C.R →ₐ[c.F] S) (z : FrPt Xo c S) (t : Ix Dw → Sˣ),
    FrMap ψ C.y z ∧ FrBor t z y ∧ v = wchar e t * ψ ⟨_, hb C⟩

theorem val_unique (hl : EvLaws Xo c) {L : Type} [Field L] [Algebra c.F L] {y : FrPt Xo c L} {v v' : L}
    (h1 : Val hb y v) (h2 : Val hb y v') : v = v' := by
  obtain ⟨C, ψ, z, t, hz, ht, rfl⟩ := h1
  obtain ⟨C', ψ', z', t', hz', ht', rfl⟩ := h2
  obtain ⟨-, hmul, hinv, -⟩ := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c L
  have := (GlobalTheory.T.values_eq_of_common_point E H Dw l Xo c hl h C C' L ψ ψ' z z' _ hz hz'
    (hmul _ _ _ _ _ ht (hinv _ _ _ ht'))).2 e b (hb C) (hb C')
  rw [this, ← mul_assoc, ← wchar_mul, mul_comm t, mul_inv_cancel_left]

theorem val_map (hl : EvLaws Xo c) {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    (φ : S →ₐ[c.F] T) {y : FrPt Xo c S} {y' : FrPt Xo c T} (hy : FrMap φ y y') {v : S} (h1 : Val hb y v) :
    Val hb y' (φ v) := by
  obtain ⟨C, ψ, z, t, hz, ht, rfl⟩ := h1
  obtain ⟨z', hz'⟩ := hl.bc S T φ z
  refine ⟨C, φ.comp ψ, z', _, frMap_trans _ _ _ ψ φ _ _ _ hz hz', frBorBC _ _ φ t z y z' y' ht hz' hy, ?_⟩
  rw [wchar_map, map_mul]; rfl

theorem val_bor {S : Type} [CommRing S] [Algebra c.F S] {t : Ix Dw → Sˣ} {y y' : FrPt Xo c S}
    (hy : FrBor t y y') {v : S} (h1 : Val hb y v) : Val hb y' (wchar e t * v) := by
  obtain ⟨C, ψ, z, t₀, hz, ht, rfl⟩ := h1
  refine ⟨C, ψ, z, t₀ * t, hz, (GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c S).2.1 _ _ _ _ _ ht hy, ?_⟩
  rw [wchar_mul]; ring

theorem val_ex (hA : Atlas h) {L : Type} [Field L] [Algebra c.F L] (y : FrPt Xo c L) : ∃ v, Val hb y v := by
  obtain ⟨C, ψ, z, t, h1, h2⟩ := hA L y
  exact ⟨_, C, ψ, z, t, h1, h2, rfl⟩

theorem val_gen (hA : Atlas h) (Z : Comp Xo c) : Val hb (genFr h Z) (b Z) := by
  obtain ⟨C, ψ, z, t, h1, h2⟩ := hA _ (genFr h Z)
  obtain rfl := chart_comp Z C ψ z t h1 h2
  refine ⟨C, C.R.val, C.yg, C.t⁻¹, C.gen, (GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c _).2.2.1 _ _ _ C.bor, ?_⟩
  show b C.Z = wchar e C.t⁻¹ * (wchar e C.t * b C.Z)
  rw [← mul_assoc, ← wchar_mul, inv_mul_cancel, wchar_one, one_mul]

def Rep {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (g s : S) : Prop :=
  ∀ (L : Type) [Field L] [Algebra c.F L] (χ : S →ₐ[c.F] L) (w : FrPt Xo c L) (v : L),
    FrMap χ y w → Val hb w v → χ g * v = χ s

theorem exists_rep (hl : EvLaws Xo c) (hA : Atlas h) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) :
    ∃ s, Rep hb y 1 s := by
  let I : Ideal S :=
    { carrier := {g | ∃ s, Rep hb y g s}
      zero_mem' := ⟨0, fun L _ _ χ w v _ _ => by simp⟩
      add_mem' := by
        rintro g g' ⟨s, hs⟩ ⟨s', hs'⟩
        exact ⟨s + s', fun L _ _ χ w v h1 h2 => by
          rw [map_add, map_add, add_mul, hs L χ w v h1 h2, hs' L χ w v h1 h2]⟩
      smul_mem' := by
        rintro r g ⟨s, hs⟩
        exact ⟨r * s, fun L _ _ χ w v h1 h2 => by
          rw [smul_eq_mul, map_mul, map_mul, mul_assoc, hs L χ w v h1 h2]⟩ }
  by_contra hne
  have hI : I ≠ ⊤ := fun hI => hne ((Ideal.eq_top_iff_one I).1 hI)
  obtain ⟨P, hP, hIP⟩ := Ideal.exists_le_maximal I hI
  have := hP.isPrime
  let χ₀ : S →ₐ[c.F] FractionRing (S ⧸ P) :=
    (IsScalarTower.toAlgHom c.F (S ⧸ P) (FractionRing (S ⧸ P))).comp (Ideal.Quotient.mkₐ c.F P)
  obtain ⟨w₀, hw₀⟩ := hl.bc _ _ χ₀ y
  obtain ⟨C, ψ₀, z₀, t₀, h1, h2⟩ := hA _ w₀
  obtain ⟨g, hg, hloc⟩ := C.opn S _ χ₀ y w₀ hw₀ ⟨ψ₀, z₀, t₀, h1, h2⟩
  let lam : S →ₐ[c.F] Localization.Away g := IsScalarTower.toAlgHom c.F S _
  have hu : IsUnit (lam g) := IsLocalization.Away.algebraMap_isUnit g
  obtain ⟨w', hw'⟩ := hl.bc _ _ lam y
  obtain ⟨ψ, z, t, h3, h4⟩ := hloc _ lam hu w' hw'
  have hv : Val hb w' (wchar e t * ψ ⟨_, hb C⟩) := ⟨C, ψ, z, t, h3, h4, rfl⟩
  generalize wchar e t * ψ ⟨_, hb C⟩ = u at hv
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj g u
  have hmem : g ^ (n + 1) ∈ I := by
    refine ⟨g * a, fun L _ _ χ w v h5 h6 => ?_⟩
    by_cases hχ : χ g = 0
    · simp [hχ]
    · let mu : Localization.Away g →ₐ[c.F] L :=
        IsLocalization.liftAlgHom (M := Submonoid.powers g) (f := χ) (by
          rintro ⟨_, k, rfl⟩
          simpa using (IsUnit.mk0 _ hχ).pow k)
      have hmu' : ∀ x, mu (algebraMap S _ x) = χ x := fun x => by
        simp [mu]
      have hmu : mu.comp lam = χ := AlgHom.ext hmu'
      have h7 : FrMap mu w' w := frMap_cancel _ _ _ lam mu y w' w hw' (by rw [hmu]; exact h5)
      have h8 := val_unique hb hl h6 (val_map hb hl mu h7 hv)
      have h9 := congrArg mu ha
      rw [map_mul, map_pow, hmu', hmu'] at h9
      rw [h8, map_mul, map_pow, ← h9]
      ring
  have hgP : g ∈ P := this.mem_of_pow_mem _ (hIP hmem)
  apply hg
  show algebraMap (S ⧸ P) (FractionRing (S ⧸ P)) (Ideal.Quotient.mk P g) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.2 hgP, map_zero]

end Val

theorem exists_sec_of_regular : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), EvLaws Xo c → ∀ h : GenFrEx Xo c, Atlas h → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (b : ∀ Z : Comp Xo c, Om Z), (∀ C : FChart h, wchar (ex Dw a n) C.t * b C.Z ∈ C.R) → ∃ g ∈ sec Xo c a n, ∀ Z, evC h Z g = b Z := by
  intro E _ _ _ H Dw l Xo c hl h hA a n b hb
  have hred : ∀ p : TRing c.F, IsReduced p.R := fun p => (Ideal.isRadical_iff_quotient_reduced p.I).1 p.rad
  choose g hg using fun (p : TRing c.F) (y : FrPt Xo c p.R) => exists_rep hb hl hA y
  have hg' : ∀ (p : TRing c.F) (y : FrPt Xo c p.R) (L : Type) [Field L] [Algebra c.F L] (χ : p.R →ₐ[c.F] L)
      (w : FrPt Xo c L) (v : L), FrMap χ y w → Val hb w v → χ (g p y) = v := by
    intro p y L _ _ χ w v h1 h2
    rw [← hg p y L χ w v h1 h2, map_one, one_mul]
  refine ⟨g, ⟨fun p q φ y z hz => ?_, fun p t y y' hy => ?_⟩, fun Z => ?_⟩
  · have := hred q
    refine eq_of_fields (K := c.F) _ _ fun L _ _ χ => ?_
    obtain ⟨w, hw⟩ := hl.bc _ _ χ z
    obtain ⟨v, hv⟩ := val_ex hb hA w
    rw [hg' q z L χ w v hw hv]
    exact (hg' p y L (χ.comp φ) w v (frMap_trans _ _ _ φ χ y z w hz hw) hv).symm
  · have := hred p
    refine eq_of_fields (K := c.F) _ _ fun L _ _ χ => ?_
    obtain ⟨w, hw⟩ := hl.bc _ _ χ y
    obtain ⟨w', hw'⟩ := hl.bc _ _ χ y'
    obtain ⟨v, hv⟩ := val_ex hb hA w
    have hv' := val_bor hb (frBorBC _ _ χ t y y' w w' hy hw hw') hv
    rw [hg' p y' L χ w' _ hw' hv', map_mul, hg' p y L χ w v hw hv, wchar_map]
  · have hh := hl.test _ (genFr h Z)
    unfold evC evR evalAt
    rw [dif_pos hh]
    exact hg' _ _ _ _ _ _ hh.choose_spec.choose_spec.choose_spec (val_gen hb hA Z)

end GlobalTheory.Reg.SecGlue
end
end

