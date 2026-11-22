import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0104
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0105
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.LinearIndependentSumElimOfExact
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecMapCompAppLE
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TranslDiffEq
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProperModelGenericFibreCompare
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GermJetUnitOnChart
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Coc.Pf

section Ring

variable {k : Type} [Field k] {d : ℕ}

theorem homAt_comp_homAt {X : Scheme.{0}} (x : Sp k ⟶ X) {A B C : Type} [CommRing A] [Algebra k A] [CommRing B]
    [Algebra k B] [CommRing C] [Algebra k C] (f : A →ₐ[k] B) (h : B →ₐ[k] C) :
    homAt x h ≫ homAt x f = homAt x (h.comp f) := by
  apply Over.OverMorphism.ext
  simp only [homAt, Over.comp_left, Over.homMk_left, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

theorem jetAug_comp_copy (n M : ℕ) (i : Fin n) :
    (jetAug : Jet k (Fin n × Fin d) M →ₐ[k] k).comp (jetCopy d M i) = jetAug := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro q
  have e : jetCopy (S := k) d M i (Ideal.Quotient.mk _ (MvPolynomial.X q)) =
      Ideal.Quotient.mk _ (MvPolynomial.X (i, q.2)) :=
    congrArg (Ideal.Quotient.mk _) (MvPolynomial.aeval_X _ q)
  have a₁ : (jetAug : Jet k (Fin n × Fin d) M →ₐ[k] k) (Ideal.Quotient.mk _ (MvPolynomial.X (i, q.2))) = 0 :=
    MvPolynomial.aeval_X _ _
  have a₂ : (jetAug : Jet k (Fin 1 × Fin d) M →ₐ[k] k) (Ideal.Quotient.mk _ (MvPolynomial.X q)) = 0 :=
    MvPolynomial.aeval_X _ _
  show (jetAug : Jet k (Fin n × Fin d) M →ₐ[k] k) (jetCopy (S := k) d M i (Ideal.Quotient.mk _ (MvPolynomial.X q))) =
    (jetAug : Jet k (Fin 1 × Fin d) M →ₐ[k] k) (Ideal.Quotient.mk _ (MvPolynomial.X q))
  rw [e, a₁, a₂]

def sub₀ (M : ℕ) : Jet k (Fin 2 × Fin d) M →ₐ[k] Jet k (Fin 1 × Fin d) M :=
  jetSubstP M fun p : Fin 2 × Fin d =>
    (![fun _ => 0, fun j => MvPolynomial.X ((0 : Fin 1), j)] : Fin 2 → Fin d → MvPolynomial (Fin 1 × Fin d) k) p.1 p.2

def trJ (m M : ℕ) (h : m ≤ M) : Jet k (Fin 1 × Fin d) M →ₐ[k] Jet k (Fin 1 × Fin d) m :=
  Ideal.Quotient.factorₐ k (Ideal.pow_le_pow_right (by omega))

theorem aug_jq (w : Fin d → k) (p m : ℕ) :
    ((jetAug : Jet (Jet k (Fin 1 × Fin d) m) Unit p →ₐ[Jet k (Fin 1 × Fin d) m] Jet k (Fin 1 × Fin d) m) :
        Jet (Jet k (Fin 1 × Fin d) m) Unit p →+* Jet k (Fin 1 × Fin d) m).comp
      ((jq w p m : _ →ₐ[k] _) : Jet k (Fin 2 × Fin d) (p + m + 1) →+* Jet (Jet k (Fin 1 × Fin d) m) Unit p) =
    ((trJ m (p + m + 1) (by omega)).comp (sub₀ (p + m + 1)) :
      Jet k (Fin 2 × Fin d) (p + m + 1) →ₐ[k] Jet k (Fin 1 × Fin d) m).toRingHom := by
  have key : ((jetAug : Jet (Jet k (Fin 1 × Fin d) m) Unit p →ₐ[Jet k (Fin 1 × Fin d) m] Jet k (Fin 1 × Fin d) m).restrictScalars k).comp
      (jq w p m) = (trJ m (p + m + 1) (by omega)).comp (sub₀ (p + m + 1)) := by
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    rintro ⟨i, j⟩
    have hq : jq w p m (Ideal.Quotient.mk _ (MvPolynomial.X (i, j))) =
        if i = 0 then algebraMap k _ (w j) * dQ (Jet k (Fin 1 × Fin d) m) p
        else inR (k := k) (Jet k (Fin 1 × Fin d) m) p (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), j))) :=
      MvPolynomial.aeval_X _ _
    have hs : sub₀ (k := k) (d := d) (p + m + 1) (Ideal.Quotient.mk _ (MvPolynomial.X (i, j))) =
        Ideal.Quotient.mk _ ((![fun _ => 0, fun j => MvPolynomial.X ((0 : Fin 1), j)] :
          Fin 2 → Fin d → MvPolynomial (Fin 1 × Fin d) k) i j - MvPolynomial.C (MvPolynomial.constantCoeff
            ((![fun _ => 0, fun j => MvPolynomial.X ((0 : Fin 1), j)] :
              Fin 2 → Fin d → MvPolynomial (Fin 1 × Fin d) k) i j))) :=
      congrArg (Ideal.Quotient.mk _) (MvPolynomial.aeval_X _ _)
    have hd : (jetAug : Jet (Jet k (Fin 1 × Fin d) m) Unit p →ₐ[Jet k (Fin 1 × Fin d) m] Jet k (Fin 1 × Fin d) m)
        (dQ (Jet k (Fin 1 × Fin d) m) p) = 0 := MvPolynomial.aeval_X _ _
    show (jetAug : Jet (Jet k (Fin 1 × Fin d) m) Unit p →ₐ[Jet k (Fin 1 × Fin d) m] Jet k (Fin 1 × Fin d) m)
        (jq w p m (Ideal.Quotient.mk _ (MvPolynomial.X (i, j)))) =
      trJ m (p + m + 1) (by omega) (sub₀ (p + m + 1) (Ideal.Quotient.mk _ (MvPolynomial.X (i, j))))
    rw [hq, hs]
    fin_cases i
    · simp only [Fin.zero_eta, if_true, map_mul, hd, mul_zero]
      simp [trJ]
    · simp [trJ, inR]
  exact congrArg AlgHom.toRingHom key

end Ring

section Pts

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)

theorem comp_psum_one {T T' : Over X0} (U : T' ⟶ T) {n : ℕ} (xs : Fin n → (T ⟶ t.G)) (h : ∀ i, U ≫ xs i = 1)
    (I : Finset (Fin n)) : U ≫ psum t.G xs I = 1 := by
  have e := psum_hom (preHom (G := t.G) U) xs I
  have e' : (fun i => preHom (G := t.G) U (xs i)) = fun _ => (1 : T' ⟶ t.G) := funext h
  rw [e'] at e
  refine e.trans ?_
  unfold psum
  induction (List.finRange n).filter (· ∈ I) with
  | nil => rfl
  | cons a l ih => exact (congrArg ((1 : T' ⟶ t.G) * ·) ih).trans (_root_.one_mul _)

end Pts

set_option maxHeartbeats 1000000 in

theorem frame_test_unit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (X0 : Scheme.{0}) (t : SAB H X0) (k : Type) [Field k] (p : ℕ) (x : Sp k ⟶ X0) (d : ℕ) (g : GermAt t x d) (w : Fin d → k) (m : ℕ) (j₀ : t.PP.L.ι), ⊤ ≤ (1 : overAt x k ⟶ t.G).left ⁻¹ᵁ t.PP.L.U j₀ → ∃ e₀ : (Jet (Jet k (Fin 1 × Fin d) m) Unit p)ˣ, (jetAug : Jet (Jet k (Fin 1 × Fin d) m) Unit p →ₐ[Jet k (Fin 1 × Fin d) m] Jet k (Fin 1 × Fin d) m) e₀ = 1 ∧ ∀ (z : Sp (Jet (Jet k (Fin 1 × Fin d) m) Unit p)) (J : (Sp (Jet (Jet k (Fin 1 × Fin d) m) Unit p) ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J → (∀ ψ : Sp (Jet (Jet k (Fin 1 × Fin d) m) Unit p) ⟶ t.G.left, ψ z ∈ t.PP.L.U j₀ → J ψ = j₀) → val (g.e (p + m + 1)) (homAt x (jq w p m)).left z J = gm (𝟙 _) z ⊤ (unitΓ e₀) := by
  intro E _ _ _ H _ X0 t k _ p x d g w m j₀ hj₀
  have hpt : ∀ (I : ULift.{0} (Finset (Fin 2))) q, ((homAt x (jq w p m)).left ≫
      cφG t ![jptG t x d g.x (p + m + 1) (0 : Fin 2), jptG t x d g.x (p + m + 1) (1 : Fin 2)] I) q ∈ t.PP.L.U j₀ := by
    intro I q
    have h0 : ∀ i : Fin 2, homAt x (jetAug : Jet k (Fin 2 × Fin d) (p + m + 1) →ₐ[k] k) ≫
        jptG t x d g.x (p + m + 1) i = 1 := by
      intro i
      rw [jptG, ← Category.assoc, homAt_comp_homAt, jetAug_comp_copy]
      exact g.chart.zero _
    have hz := comp_psum_one t (homAt x (jetAug : Jet k (Fin 2 × Fin d) (p + m + 1) →ₐ[k] k))
      ![jptG t x d g.x (p + m + 1) (0 : Fin 2), jptG t x d g.x (p + m + 1) (1 : Fin 2)]
      (by intro i; fin_cases i; exacts [h0 0, h0 1]) I.down
    rw [Scheme.Hom.comp_apply]
    exact jet_left_mem t x j₀ hj₀ _ hz _
  have hred : ∀ (z' : Sp (Jet k (Fin 1 × Fin d) m)) (J' : (Sp (Jet k (Fin 1 × Fin d) m) ⟶ t.G.left) → t.PP.L.ι),
      Good t.PP.L z' J' → val (g.e (p + m + 1))
        (spMap ((jetAug : Jet (Jet k (Fin 1 × Fin d) m) Unit p →ₐ[Jet k (Fin 1 × Fin d) m] Jet k (Fin 1 × Fin d) m) :
          Jet (Jet k (Fin 1 × Fin d) m) Unit p →+* Jet k (Fin 1 × Fin d) m) ≫ (homAt x (jq w p m)).left) z' J' = 1 := by
    intro z' J' hJ'
    have e : spMap ((jetAug : Jet (Jet k (Fin 1 × Fin d) m) Unit p →ₐ[Jet k (Fin 1 × Fin d) m] Jet k (Fin 1 × Fin d) m) :
          Jet (Jet k (Fin 1 × Fin d) m) Unit p →+* Jet k (Fin 1 × Fin d) m) ≫ (homAt x (jq w p m)).left =
        spMap ((trJ m (p + m + 1) (by omega) : Jet k (Fin 1 × Fin d) (p + m + 1) →ₐ[k] _) :
          Jet k (Fin 1 × Fin d) (p + m + 1) →+* Jet k (Fin 1 × Fin d) m) ≫ (homAt x (sub₀ (p + m + 1))).left := by
      have := aug_jq w p m
      simp only [homAt, Over.homMk_left, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      rw [this]
      rfl
    rw [e, ← val_pull hJ' (g.e (p + m + 1)) (homAt x (sub₀ (p + m + 1))).left]
    exact (val_corr hJ' (g.axes (p + m + 1)).1 _).trans (val_one _)
  obtain ⟨e₀, he, hv⟩ := GlobalTheory.CompanionTheory.Ar.Coc.val_eq_unit_of_red t.G.left (Sp (Jet k (Fin 2 × Fin d) (p + m + 1))) t.PP.L t.PP.isLB
    (Jet k (Fin 1 × Fin d) m) p (ULift (Finset (Fin 2)))
    (cφG t ![jptG t x d g.x (p + m + 1) (0 : Fin 2), jptG t x d g.x (p + m + 1) (1 : Fin 2)]) (cε 2) (g.e (p + m + 1))
    (homAt x (jq w p m)).left j₀ hpt (fun z' J' hJ' _ => hred z' J' hJ')
  exact ⟨e₀, he, fun z J hJ hc => hv z J hJ fun I => hc _ (hpt I z)⟩

end GlobalTheory.CompanionTheory.Ar.Coc.Pf
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GradedDegreeFormula
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GrLine

open GroundTheory.Heights₂.Heights

section Algebra

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem linearIndependent_snoc {F : Submodule R M}
    (hsat : ∀ (a : R) (x : M), a ≠ 0 → a • x ∈ F → x ∈ F) {n : ℕ} {f : Fin n → M}
    (hf : ∀ a, f a ∈ F) (hli : LinearIndependent R f) {s : M} (hs : s ∉ F) :
    LinearIndependent R (Fin.snoc f s : Fin (n + 1) → M) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  rw [Fin.sum_univ_castSucc] at hg
  simp only [Fin.snoc_castSucc, Fin.snoc_last] at hg
  have hlast : g (Fin.last n) = 0 := by
    by_contra h0
    apply hs
    apply hsat _ _ h0
    have : g (Fin.last n) • s = -∑ a : Fin n, g a.castSucc • f a := eq_neg_of_add_eq_zero_right hg
    rw [this]
    exact F.neg_mem (F.sum_mem fun a _ => F.smul_mem _ (hf a))
  rw [hlast, zero_smul, add_zero] at hg
  have hz := Fintype.linearIndependent_iff.mp hli (fun a => g a.castSucc) hg
  intro j
  exact Fin.lastCases hlast (fun a => hz a) j

theorem card_quotient_line {F G P : Submodule R M} (hFG : F ≤ G) (hPF : P ≤ F)
    (hsat : ∀ (a : R) (x : M), a ≠ 0 → a • x ∈ F → x ∈ F) {s : M} (hs : s ∉ F)
    (T : Submodule R G) (U : Submodule R F)
    (hT : ∀ x : G, x ∈ T ↔ (x : M) ∈ P ⊔ Submodule.span R {s})
    (hU : ∀ x : F, x ∈ U ↔ (x : M) ∈ P) :
    Nat.card (G ⧸ T) =
      Nat.card (G ⧸ (F ⊔ Submodule.span R {s}).comap G.subtype) * Nat.card (F ⧸ U) := by
  set S : Submodule R G := (F ⊔ Submodule.span R {s}).comap G.subtype with hS
  have hTS : T ≤ S := fun x hx => (sup_le_sup_right hPF _) ((hT x).1 hx)
  let φ : F →ₗ[R] G ⧸ T := T.mkQ ∘ₗ Submodule.inclusion hFG
  have hker : LinearMap.ker φ = U := by
    ext x
    rw [hU]
    simp only [φ, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    rw [hT]
    change (x : M) ∈ P ⊔ Submodule.span R {s} ↔ _
    constructor
    · intro h
      obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 h
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hz
      have ha : a = 0 := by
        by_contra h0
        apply hs
        apply hsat a s h0
        have : a • s = (x : M) - y := by rw [← hyz]; abel
        rw [this]
        exact F.sub_mem x.2 (hPF hy)
      rw [ha, zero_smul, add_zero] at hyz
      rwa [← hyz]
    · exact fun h => Submodule.mem_sup_left h
  have hrange : LinearMap.range φ = S.map T.mkQ := by
    ext q
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨Submodule.inclusion hFG x, Submodule.mem_sup_left x.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨x, hx, z, hz, hxz⟩ := Submodule.mem_sup.1 (show (y : M) ∈ F ⊔ Submodule.span R {s} from hy)
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hz
      refine ⟨⟨x, hx⟩, ?_⟩
      simp only [φ, LinearMap.comp_apply, Submodule.mkQ_apply]
      rw [Submodule.Quotient.eq, hT]
      have : ((Submodule.inclusion hFG ⟨x, hx⟩ - y : G) : M) = -(a • s) := by
        change x - (y : M) = _
        rw [← hxz]
        abel
      rw [this]
      exact neg_mem (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self s)))
  have hc : Nat.card (F ⧸ U) = Nat.card (S.map T.mkQ) := by
    rw [← hker, ← hrange]
    exact Nat.card_congr φ.quotKerEquivRange.toEquiv
  rw [hc, mul_comm]
  exact (Submodule.card_quotient_mul_card_quotient S T hTS).symm

end Algebra

open scoped ComplexOrder in

theorem gramDet_re_eq_norm {L : Type} [Field L] [NumberField L] (B : HermitianBundle.{0} L)
    (σ : L →+* ℂ) {n : ℕ} {e : Fin n → B.carrier} (hli : LinearIndependent (𝓞 L) e) :
    GroundTheory.Heights₂.Heights.gramDet B.metric σ e = ‖B.gramDet σ e‖ := by
  have hd : B.gramDet σ e = (Matrix.gram ℂ fun i => fibreVec B.metric σ (e i)).det := rfl
  have hp : 0 < (Matrix.gram ℂ fun i => fibreVec B.metric σ (e i)).det :=
    (Matrix.posDef_gram_of_linearIndependent (linearIndependent_fibreVec B.metric σ hli)).det_pos
  obtain ⟨h1, h2⟩ := Complex.lt_def.mp hp
  have hz : (((Matrix.gram ℂ fun i => fibreVec B.metric σ (e i)).det).re : ℂ) =
      (Matrix.gram ℂ fun i => fibreVec B.metric σ (e i)).det :=
    Complex.ext (by simp) (by simpa using h2)
  rw [hd, ← hz, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by simpa using h1)]
  rfl

theorem grDeg_eq : ∀ (L : Type) [Field L] [NumberField L] (B : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (r : ℕ) (A : SatFlag B r) (i : Fin r) (f : Fin i → B.carrier) (s : B.carrier), (∀ a, f a ∈ A.F i.castSucc) → LinearIndependent (𝓞 L) f → s ∈ A.F i.succ → s ∉ A.F i.castSucc → A.grDeg i = (Module.finrank ℚ L : ℝ)⁻¹ * (Real.log (Nat.card (A.F i.succ ⧸ (A.F i.castSucc ⊔ Submodule.span (𝓞 L) {s}).comap (A.F i.succ).subtype)) - (1 / 2) * ∑ σ : L →+* ℂ, (Real.log ‖B.gramDet σ (Fin.snoc f s : Fin (i + 1) → B.carrier)‖ - Real.log ‖B.gramDet σ f‖)) := by
  intro L _ _ B r A i f s hf hli hs hs0
  have hFG : A.F i.castSucc ≤ A.F i.succ := A.mono (Fin.castSucc_lt_succ).le
  have hsat : ∀ (a : 𝓞 L) (x : B.carrier), a ≠ 0 → a • x ∈ A.F i.castSucc → x ∈ A.F i.castSucc :=
    A.sat i.castSucc
  have hsn : LinearIndependent (𝓞 L) (Fin.snoc f s : Fin (i + 1) → B.carrier) :=
    linearIndependent_snoc hsat hf hli hs0
  have hmem : ∀ a, (Fin.snoc f s : Fin (i + 1) → B.carrier) a ∈ A.F i.succ := by
    intro a
    refine Fin.lastCases ?_ (fun j => ?_) a
    · simpa using hs
    · simpa using hFG (hf j)
  let f' : Fin i → A.F i.castSucc := fun a => ⟨f a, hf a⟩
  let g' : Fin (i + 1) → A.F i.succ := fun a => ⟨(Fin.snoc f s : Fin (i + 1) → B.carrier) a, hmem a⟩
  have hf' : LinearIndependent (𝓞 L) f' := LinearIndependent.of_comp (A.F i.castSucc).subtype hli
  have hg' : LinearIndependent (𝓞 L) g' := LinearIndependent.of_comp (A.F i.succ).subtype hsn
  have hcF : Fintype.card (Fin i) = B.rank (A.F i.castSucc) := by
    rw [Fintype.card_fin, A.rank]; simp
  have hcG : Fintype.card (Fin (i + 1)) = B.rank (A.F i.succ) := by
    rw [Fintype.card_fin, A.rank]; simp
  have hP : Submodule.span (𝓞 L) (Set.range f) ≤ A.F i.castSucc :=
    Submodule.span_le.2 (by rintro _ ⟨a, rfl⟩; exact hf a)
  have hU : ∀ x : A.F i.castSucc, x ∈ Submodule.span (𝓞 L) (Set.range f') ↔
      (x : B.carrier) ∈ Submodule.span (𝓞 L) (Set.range f) := by
    intro x
    have hm : (Submodule.span (𝓞 L) (Set.range f')).map (A.F i.castSucc).subtype =
        Submodule.span (𝓞 L) (Set.range f) := by
      rw [Submodule.map_span, ← Set.range_comp]
      rfl
    rw [← hm]
    constructor
    · exact fun h => ⟨x, h, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      rwa [← Subtype.ext hyx]
  have hT : ∀ x : A.F i.succ, x ∈ Submodule.span (𝓞 L) (Set.range g') ↔
      (x : B.carrier) ∈ Submodule.span (𝓞 L) (Set.range f) ⊔ Submodule.span (𝓞 L) {s} := by
    intro x
    have hm : (Submodule.span (𝓞 L) (Set.range g')).map (A.F i.succ).subtype =
        Submodule.span (𝓞 L) (Set.range f) ⊔ Submodule.span (𝓞 L) {s} := by
      rw [Submodule.map_span, ← Set.range_comp, ← Submodule.span_union]
      congr 1
      have hr : Set.range ((A.F i.succ).subtype ∘ g') =
          Set.range (Fin.snoc f s : Fin (i + 1) → B.carrier) := rfl
      rw [hr]
      ext y
      constructor
      · rintro ⟨a, rfl⟩
        refine Fin.lastCases ?_ (fun j => ?_) a
        · right; simp
        · left; exact ⟨j, by simp⟩
      · rintro (⟨j, rfl⟩ | hy)
        · exact ⟨j.castSucc, by simp⟩
        · exact ⟨Fin.last _, by simpa using hy.symm⟩
    rw [← hm]
    constructor
    · exact fun h => ⟨x, h, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      rwa [← Subtype.ext hyx]
  have hidx := card_quotient_line hFG hP hsat hs0 _ _ hT hU
  have hfinF : Finite (A.F i.castSucc ⧸ Submodule.span (𝓞 L) (Set.range f')) :=
    finite_quotient_span hf' hcF
  have hfinG : Finite (A.F i.succ ⧸ Submodule.span (𝓞 L) (Set.range g')) :=
    finite_quotient_span hg' hcG
  have hne : (Nat.card (A.F i.succ ⧸ Submodule.span (𝓞 L) (Set.range g')) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  have hlog : Real.log (Nat.card (A.F i.succ ⧸ Submodule.span (𝓞 L) (Set.range g'))) =
      Real.log (Nat.card (A.F i.succ ⧸ (A.F i.castSucc ⊔ Submodule.span (𝓞 L) {s}).comap (A.F i.succ).subtype)) +
        Real.log (Nat.card (A.F i.castSucc ⧸ Submodule.span (𝓞 L) (Set.range f'))) := by
    rw [hidx] at hne ⊢
    push_cast at hne ⊢
    exact Real.log_mul (left_ne_zero_of_mul hne) (right_ne_zero_of_mul hne)
  have hgF : ∀ σ : L →+* ℂ, GroundTheory.Heights₂.Heights.gramDet B.metric σ
      (fun a => ((f' a : A.F i.castSucc) : B.carrier)) = ‖B.gramDet σ f‖ :=
    fun σ => gramDet_re_eq_norm B σ hli
  have hgG : ∀ σ : L →+* ℂ, GroundTheory.Heights₂.Heights.gramDet B.metric σ
      (fun a => ((g' a : A.F i.succ) : B.carrier)) =
        ‖B.gramDet σ (Fin.snoc f s : Fin (i + 1) → B.carrier)‖ :=
    fun σ => gramDet_re_eq_norm B σ hsn
  rw [SatFlag.grDeg, HermitianBundle.normDegree, HermitianBundle.normDegree,
    B.degree_eq_of_linearIndependent _ hf' hcF, B.degree_eq_of_linearIndependent _ hg' hcG, hlog]
  simp only [hgF, hgG, Finset.sum_sub_distrib]
  ring

end GlobalTheory.CompanionTheory.Ar.GrLine
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSubFibreSubFib
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagFib

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {G : Over X} [GrpObj G] {ξ : Sp Ω ⟶ X}
  {Li : Type} [AddCommGroup Li] [Module Ω Li] {L : Type} [Field L] [NumberField L]

def subGens (M : LieModel G ξ Li) (U : Submodule Ω Li) (z : Sp (𝓞 L) ⟶ X) {V : Type} [AddCommGroup V]
    [Module (𝓞 L) V] (MB : LieModel G z V) : Set V :=
  {x' | ∃ e ∈ U, ∃ v : epsAt (spMap (algebraMap (𝓞 L) L) ≫ z) ⟶ G,
    M.ValAt (spMap (algebraMap (𝓞 L) L) ≫ z) e v ∧ MB.Lifts (algebraMap (𝓞 L) L) (𝟙 G.left) x' v}

def subFib (M : LieModel G ξ Li) (U : Submodule Ω Li) (z : Sp (𝓞 L) ⟶ X) {V : Type} [AddCommGroup V]
    [Module (𝓞 L) V] (MB : LieModel G z V) : Submodule (𝓞 L) V where
  carrier := {x | ∃ a : 𝓞 L, a ≠ 0 ∧ a • x ∈ Submodule.span (𝓞 L) (subGens M U z MB)}
  add_mem' := by
    rintro x y ⟨a, ha, hx⟩ ⟨b, hb, hy⟩
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact Submodule.smul_mem _ _ hx
    · rw [mul_smul]; exact Submodule.smul_mem _ _ hy
  zero_mem' := ⟨1, one_ne_zero, by simp⟩
  smul_mem' := by
    rintro c x ⟨a, ha, hx⟩
    refine ⟨a, ha, ?_⟩
    rw [smul_comm]; exact Submodule.smul_mem _ _ hx

theorem mem_subFib {M : LieModel G ξ Li} {U : Submodule Ω Li} {z : Sp (𝓞 L) ⟶ X} {V : Type} [AddCommGroup V]
    [Module (𝓞 L) V] {MB : LieModel G z V} {x : V} :
    x ∈ subFib M U z MB ↔ ∃ a : 𝓞 L, a ≠ 0 ∧ a • x ∈ Submodule.span (𝓞 L) (subGens M U z MB) := Iff.rfl

theorem isSubFibre_subFib (M : LieModel G ξ Li) (U : Submodule Ω Li) (z : Sp (𝓞 L) ⟶ X) {V : Type} [AddCommGroup V]
    [Module (𝓞 L) V] (MB : LieModel G z V) : IsSubFibre M U z MB (subFib M U z MB) := fun _ => Iff.rfl

theorem subFib_mono (M : LieModel G ξ Li) {U U' : Submodule Ω Li} (h : U ≤ U') (z : Sp (𝓞 L) ⟶ X) {V : Type}
    [AddCommGroup V] [Module (𝓞 L) V] (MB : LieModel G z V) : subFib M U z MB ≤ subFib M U' z MB := by
  rintro x ⟨a, ha, hx⟩
  refine ⟨a, ha, Submodule.span_mono ?_ hx⟩
  rintro y ⟨e, he, r⟩
  exact ⟨e, h he, r⟩

theorem subFib_saturated (M : LieModel G ξ Li) (U : Submodule Ω Li) (z : Sp (𝓞 L) ⟶ X)
    (B : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (MB : LieModel G z B.carrier) : B.Saturated (subFib M U z MB) := by
  rintro a x ha ⟨b, hb, hx⟩
  exact ⟨b * a, mul_ne_zero hb ha, by rwa [mul_smul]⟩

end GlobalTheory.CompanionTheory.Ar.FlagFib
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IteratedDerivativeFactor
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
open GlobalTheory.CompanionTheory.Ar.InvDer
open scoped Topology

namespace GlobalTheory.CompanionTheory.Ar.JetLeib

theorem jet_mul_first {u v : ℂ → ℂ} (hu : AnalyticAt ℂ u 0) (hv : AnalyticAt ℂ v 0) (i : ℕ)
    (h0 : ∀ k < i, iteratedDeriv k u 0 = 0) :
    (∀ k < i, iteratedDeriv k (fun t => u t * v t) 0 = 0) ∧
      iteratedDeriv i (fun t => u t * v t) 0 = v 0 * iteratedDeriv i u 0 := by
  have key : ∀ n : ℕ, iteratedDeriv n (fun t => u t * v t) 0 =
      ∑ m ∈ Finset.range (n + 1),
        (n.choose m : ℂ) * iteratedDeriv m u 0 * iteratedDeriv (n - m) v 0 := fun n =>
    iteratedDeriv_fun_mul hu.contDiffAt hv.contDiffAt
  refine ⟨fun k hk => ?_, ?_⟩
  · rw [key k]
    refine Finset.sum_eq_zero fun m hm => ?_
    have hmk : m < i := lt_of_le_of_lt (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)) hk
    rw [h0 m hmk]
    simp
  · rw [key i, Finset.sum_range_succ, Finset.sum_eq_zero, zero_add]
    · simp [mul_comm]
    · intro m hm
      rw [h0 m (Finset.mem_range.mp hm)]
      simp

theorem jet_first_nonzero : ∀ (r : ℕ) (Ψ : Fin r → ℂ → ℂ) (c : Fin r → ℂ) (h F : ℂ → ℂ), (∀ j, AnalyticAt ℂ (Ψ j) 0) → AnalyticAt ℂ F 0 → F 0 ≠ 0 → (∀ᶠ τ in 𝓝 (0 : ℂ), ∑ j, c j * Ψ j τ = h τ * F τ) → ∀ i : ℕ, ((∀ k < i, ∑ j, c j * iteratedDeriv k (Ψ j) 0 = 0) ↔ ∀ k < i, iteratedDeriv k h 0 = 0) ∧ ((∀ k < i, ∑ j, c j * iteratedDeriv k (Ψ j) 0 = 0) → ∑ j, c j * iteratedDeriv i (Ψ j) 0 = F 0 * iteratedDeriv i h 0) := by
  intro r Ψ c h F hΨ hF hF0 hev i
  have hP : AnalyticAt ℂ (fun τ => ∑ j, c j * Ψ j τ) 0 :=
    Finset.analyticAt_fun_sum _ fun j _ => analyticAt_const.mul (hΨ j)
  have hDP : ∀ k : ℕ, iteratedDeriv k (fun τ => ∑ j, c j * Ψ j τ) 0 =
      ∑ j, c j * iteratedDeriv k (Ψ j) 0 := by
    intro k
    have hc : ∀ j ∈ (Finset.univ : Finset (Fin r)),
        ContDiffAt ℂ k (fun τ => c j * Ψ j τ) 0 := fun j _ =>
      (analyticAt_const.mul (hΨ j)).contDiffAt
    rw [iteratedDeriv_fun_sum (f := fun j τ => c j * Ψ j τ) hc]
    exact Finset.sum_congr rfl fun j _ => iteratedDeriv_const_mul_field (c j) (Ψ j)
  have hFi : AnalyticAt ℂ (fun t => (F t)⁻¹) 0 := hF.inv hF0
  have hne : ∀ᶠ τ in 𝓝 (0 : ℂ), F τ ≠ 0 := hF.continuousAt.eventually_ne hF0
  have hh : h =ᶠ[𝓝 (0 : ℂ)] fun t => (∑ j, c j * Ψ j t) * (F t)⁻¹ := by
    filter_upwards [hev, hne] with τ h1 h2
    rw [h1, _root_.mul_assoc, mul_inv_cancel₀ h2, _root_.mul_one]
  have hha : AnalyticAt ℂ h 0 := (hP.mul hFi).congr hh.symm
  have hPe : (fun τ => ∑ j, c j * Ψ j τ) =ᶠ[𝓝 (0 : ℂ)] fun t => h t * F t := hev
  have hDPh : ∀ k : ℕ, ∑ j, c j * iteratedDeriv k (Ψ j) 0 =
      iteratedDeriv k (fun t => h t * F t) 0 := fun k => by
    rw [← hDP k]; exact hPe.iteratedDeriv_eq k
  have hDh : ∀ k : ℕ, iteratedDeriv k h 0 =
      iteratedDeriv k (fun t => (∑ j, c j * Ψ j t) * (F t)⁻¹) 0 := fun k =>
    hh.iteratedDeriv_eq k
  have back : (∀ k < i, ∑ j, c j * iteratedDeriv k (Ψ j) 0 = 0) →
      ∀ k < i, iteratedDeriv k h 0 = 0 := by
    intro hz k hk
    rw [hDh k]
    exact (jet_mul_first hP hFi i fun k hk => by rw [hDP k]; exact hz k hk).1 k hk
  refine ⟨⟨back, fun hz k hk => ?_⟩, fun hz => ?_⟩
  · rw [hDPh k]
    exact (jet_mul_first hha hF i hz).1 k hk
  · rw [hDPh i]
    exact (jet_mul_first hha hF i (back hz)).2

end GlobalTheory.CompanionTheory.Ar.JetLeib
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LineBundleSectionDifferenceGeneratorStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.line_bundle_section_difference_generator : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (k : Type) [Field k] (p : ℕ) (f f' : Sp (Jet k Unit p) ⟶ X), spMap ((jetAug : Jet k Unit p →ₐ[k] k) : Jet k Unit p →+* k) ≫ f = spMap ((jetAug : Jet k Unit p →ₐ[k] k) : Jet k Unit p →+* k) ≫ f' → ∃ τ : LB.Gen (LB.LinComb L (K := Fin 2) ![f, f'] ![1, -1]), τ.IsGen ∧ ∀ (Z' : Scheme.{0}) (r : Z' ⟶ Sp k) (z : Z') (J : (Z' ⟶ X) → L.ι), Good L z J → val τ (r ≫ spMap ((jetAug : Jet k Unit p →ₐ[k] k) : Jet k Unit p →+* k)) z J = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Coc.jetPair_gen | exact GlobalTheory.CompanionTheory.Ar.Coc.jetPair_gen | (intros; apply GlobalTheory.CompanionTheory.Ar.Coc.jetPair_gen <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LineHeightInvariantScalingStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.line_height_invariant_scaling : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (A : HermLine ι) (L : Type) [Field L] [NumberField L] (L' : Type) [Field L'] [NumberField L'] (e : L →+* L') (w : (Σ k, ι k) → L) (c : K → L'), (∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) → (∀ k, c k ≠ 0) → lineHt A L' (fun p => c p.1 * e (w p)) = lineHt A L w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Ht.lineHt_map_scale | exact GlobalTheory.CompanionTheory.Ar.Ht.lineHt_map_scale | (intros; apply GlobalTheory.CompanionTheory.Ar.Ht.lineHt_map_scale <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProperModelGenericFibreCompareStatement
section
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.proper_model_generic_fibre_compare : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) [CharZero Ω] (O : Type) [CommRing O] [IsDomain O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)) [IsNoetherianRing O] [IsProper s] (X' : Scheme.{0}) (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω') (C : Type) [Field C] [Algebra O C] [Algebra C Ω'] (s' : X' ⟶ Spec (CommRingCat.of C)), ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → Function.Injective (algebraMap O Ω) → Function.Injective (algebraMap O C) → IsPullback f s' s (Spec.map (CommRingCat.ofHom (algebraMap O C))) → ξ' ≫ s' = Spec.map (CommRingCat.ofHom (algebraMap C Ω')) → Dominates ξ' ξ f i → IsCptGen ξ → IsCptGen ξ' → ConstClosed O Ω → ∀ (L : Lat ξ Ω) (t' : Ω'), L.IsVBOn (genFibre O ξ) 1 ⊤ → (∀ p' : Cpt ξ', (L.pull ξ' f i.toAddMonoidHom).IsGenAt p' t') → ∃ (t : Ω) (c : C), (∀ p ∈ genFibre O ξ, L.IsGenAt p t) ∧ t' = algebraMap C Ω' c * i t := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.exists_gen_of_extension | exact GlobalTheory.CompanionTheory.Ar.Flat.exists_gen_of_extension | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.exists_gen_of_extension <;> assumption)
end

