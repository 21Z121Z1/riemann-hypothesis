import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1633
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1570
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1578
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1036
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.ZeroNotAdmissibleOfRankPos
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0435
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1060
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1124
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1175
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1627
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1644
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1589
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1623
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1631
import Formalism.LocalToGlobal.Divisibility.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutingMonicOperatorPolynomials
section
open Matrix GlobalTheory.LeviHC
open Formalism.REAL (GlRel qdet)

noncomputable section

namespace GlobalTheory.LeviHC.FactorMod

variable {M : Type} [AddCommGroup M] [Module ℂ M]

theorem finMod_mono {K₁ K₂ : Submodule ℂ M} (h : K₁ ≤ K₂) {A : Subalgebra ℂ (Module.End ℂ M)} {v : M}
    (hf : FinMod K₁ A v) : FinMod K₂ A v := by
  unfold FinMod at *
  have e : Submodule.span ℂ {y : M ⧸ K₂ | ∃ a ∈ A, y = K₂.mkQ (a v)} =
      (Submodule.span ℂ {y : M ⧸ K₁ | ∃ a ∈ A, y = K₁.mkQ (a v)}).map (Submodule.factor h) := by
    rw [Submodule.map_span]
    congr 1
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨K₁.mkQ (a v), ⟨a, ha, rfl⟩, Submodule.factor_mk h _⟩
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨a, ha, Submodule.factor_mk h _⟩
  rw [e]
  infer_instance

theorem comm_of_mem_adjoin {s : Set (Module.End ℂ M)} {f b : Module.End ℂ M} (hb : b ∈ Algebra.adjoin ℂ s)
    (h : ∀ g ∈ s, Commute f g) : Commute f b := by
  have hle : Algebra.adjoin ℂ s ≤ Subalgebra.centralizer ℂ {f} :=
    Algebra.adjoin_le fun g hg => (Subalgebra.mem_centralizer_iff ℂ).2 fun y hy => by
      rw [Set.mem_singleton_iff.1 hy]; exact (h g hg)
  exact (((Subalgebra.mem_centralizer_iff ℂ).1 (hle hb)) f rfl)

def core (K : Submodule ℂ M) (S : Subalgebra ℂ (Module.End ℂ M)) : Submodule ℂ M where
  carrier := {x | ∀ b ∈ S, b x ∈ K}
  add_mem' := fun hx hy b hb => by rw [map_add]; exact K.add_mem (hx b hb) (hy b hb)
  zero_mem' := fun b _ => by rw [map_zero]; exact K.zero_mem
  smul_mem' := fun c x hx b hb => by rw [map_smul]; exact K.smul_mem c (hx b hb)

theorem core_le (K : Submodule ℂ M) (S : Subalgebra ℂ (Module.End ℂ M)) : core K S ≤ K := fun x hx => by
  simpa using hx 1 S.one_mem

theorem finMod_factor : ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (M' K : Submodule ℂ M) (c p q : ℂ → Module.End ℂ M),
 (∃ (d : ℕ) (a : ℕ → Module.End ℂ M), a d = 1 ∧ ∀ u, p u = ∑ i ∈ Finset.range (d + 1), u ^ i • a i) →
 (∃ (d : ℕ) (a : ℕ → Module.End ℂ M), a d = 1 ∧ ∀ u, q u = ∑ i ∈ Finset.range (d + 1), u ^ i • a i) →
 (∀ u u', Commute (p u) (p u')) → (∀ u u', Commute (q u) (q u')) → (∀ u u', Commute (p u) (q u')) → (∀ u u', Commute (c u) (q u')) →
 (∀ u, ∀ x ∈ M', c u x ∈ M' ∧ p u x ∈ M' ∧ q u x ∈ M') → (∀ u, ∀ x ∈ K, p u x ∈ K) →
 (∀ u, ∀ x ∈ M', c u x - p u (q u x) ∈ K) →
 ∀ v ∈ M', FinMod ⊥ (Algebra.adjoin ℂ (Set.range c)) v → FinMod K (Algebra.adjoin ℂ (Set.range p)) v := by
  intro M _ _ M' K c p q hp hq hpp hqq hpq hcq hM hK hrel v hv hfin
  set S := Algebra.adjoin ℂ (Set.range q) with hS

  have cb : ∀ u, ∀ b ∈ S, Commute (c u) b := fun u b hb =>
    comm_of_mem_adjoin hb (by rintro _ ⟨u', rfl⟩; exact hcq u u')
  have pb : ∀ u, ∀ b ∈ S, Commute (p u) b := fun u b hb =>
    comm_of_mem_adjoin hb (by rintro _ ⟨u', rfl⟩; exact hpq u u')
  have qb : ∀ u, ∀ b ∈ S, Commute (q u) b := fun u b hb =>
    comm_of_mem_adjoin hb (by rintro _ ⟨u', rfl⟩; exact hqq u u')

  have hSM : ∀ b ∈ S, ∀ x ∈ M', b x ∈ M' := by
    have hle : S ≤ GlobalTheory.LeviHC.MidBlock.stab M' :=
      Algebra.adjoin_le (by rintro _ ⟨u, rfl⟩ x hx; exact (hM u x hx).2.2)
    intro b hb x hx
    exact hle hb x hx
  set K' := core K S
  have hK'p : ∀ u, ∀ x ∈ K', p u x ∈ K' ∧ q u x ∈ K' := by
    intro u x hx
    refine ⟨fun b hb => ?_, fun b hb => ?_⟩
    · have e : b (p u x) = p u (b x) := by
        have := (pb u b hb).eq
        exact (congrArg (fun f : Module.End ℂ M => f x) this).symm
      rw [e]; exact hK u _ (hx b hb)
    · have : b * q u ∈ S := S.mul_mem hb (Algebra.subset_adjoin ⟨u, rfl⟩)
      exact hx _ this
  have hrel' : ∀ u, ∀ x ∈ M', c u x - p u (q u x) ∈ K' := by
    intro u x hx b hb
    have e1 : b (c u x) = c u (b x) := (congrArg (fun f : Module.End ℂ M => f x) (cb u b hb).eq).symm
    have e2 : b (q u x) = q u (b x) := (congrArg (fun f : Module.End ℂ M => f x) (qb u b hb).eq).symm
    have e3 : b (p u (q u x)) = p u (b (q u x)) :=
      (congrArg (fun f : Module.End ℂ M => f (q u x)) (pb u b hb).eq).symm
    rw [map_sub, e1, e3, e2]
    exact hrel u _ (hSM b hb x hx)
  have h1 : FinMod K' (Algebra.adjoin ℂ (Set.range c)) v := finMod_mono bot_le hfin
  have h2 := GlobalTheory.LeviHC.QuotMonic.monicFactorFiniteMod_of GlobalTheory.LeviHC.monicFactorFinite M M' K' c p q hp hq hpp hqq hpq
    hM hK'p hrel' v hv h1
  exact finMod_mono (core_le K S) h2

end GlobalTheory.LeviHC.FactorMod

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoprimeScalarForEmbedding
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature GlobalTheory.GalLift GlobalTheory.GalOne

namespace GlobalTheory.GalOne

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}

theorem pairL_levRep_zsmul {n : ℕ} (x : Fin n → Dw.La) (m : ℤ) (q : Fin n → LevQ Dw l) :
    (l.M : ℤ) ∣ pairL (l := l) x (fun b => levRep ((m • q) b)) - m * pairL (l := l) x (fun b => levRep (q b)) := by
  have hrep : ∀ q : LevQ Dw l, (Submodule.Quotient.mk (levRep q) : LevQ Dw l) = q := fun q =>
    Classical.choose_spec (Submodule.Quotient.mk_surjective _ q)
  have e : m * pairL (l := l) x (fun b => levRep (q b)) = pairL (l := l) x (fun b => m • levRep (q b)) := by
    unfold pairL
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [smul_comm, map_zsmul, smul_eq_mul]
  rw [e]
  refine GlobalTheory.LevelPairing.pairL_congr _ _ _ _ (fun b => by simp) fun b => ?_
  rw [← Submodule.Quotient.eq, hrep]
  refine Eq.trans ?_ (map_zsmul (Submodule.mkQ _) m (levRep (q b))).symm
  rw [Submodule.mkQ_apply, hrep, Pi.smul_apply]

theorem map_phiHat (c : Coeff l) (τ : c.F →+* ℂ) : ∃ m : ℤ, IsCoprime m (l.M : ℤ) ∧
    ∀ (n : ℕ) (φ : (Fin n → LevQc Dw l) → c.F), (∀ x, φ x = 0 ∨ φ x = 1) → ∀ q,
      τ (phiHat c φ q) = c.F.val.toRingHom (phiHat c φ (m • q)) := by
  have hM : l.M ≠ 0 := by have := l.three_le; omega
  haveI : NeZero l.M := ⟨hM⟩
  have h0 := GlobalTheory.LevelPairing.zetaM_prim c
  have h1 : IsPrimitiveRoot (c.F.val.toRingHom (zetaM c)) l.M := h0.map_of_injective c.F.val.toRingHom.injective
  have h2 : IsPrimitiveRoot (τ (zetaM c)) l.M := h0.map_of_injective τ.injective
  obtain ⟨m, -, hm⟩ := h1.eq_pow_of_pow_eq_one h2.pow_eq_one
  have hc : m.Coprime l.M := (h1.pow_iff_coprime (Nat.pos_of_ne_zero hM) m).1 (hm ▸ h2)
  refine ⟨m, Nat.isCoprime_iff_coprime.2 hc, fun n φ hφ q => ?_⟩
  haveI := GlobalTheory.AdTh.PairModel.finite_levQc Dw l
  haveI := Fintype.ofFinite (Fin n → LevQc Dw l)
  rw [phiHat, phiHat, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, map_sum, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [GlobalTheory.LevelPairing.zpow_congr c (pairL_levRep_zsmul _ (m : ℤ) q), map_mul, map_mul, map_zpow₀, map_zpow₀, ← hm,
    _root_.zpow_mul, zpow_natCast]
  congr 1
  rcases hφ x with h | h <;> simp [h]

end Gen

end GlobalTheory.GalOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreDictionaryGoodAtGoodEmbedding
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict

theorem castDict_laws {D : D7} {V W : HSp D} (hV : V = W) {r : ℕ} (hr : W.rank = r) {Comp : Type}
    (X : Comp → ReciprocityTheory.ChartRestriction.G.FD.Data D.host.E r) (dict : GA D V → Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame (X k).Ψ r)
    (mu : GA D V → ℂ) (Kf : Subgroup (GA D V)) (Kf' : Subgroup (GA D W))
    (hK : ∀ g : GA D W, g ∈ Kf' ↔ cast (congrArg (GA D) hV.symm) g ∈ Kf)
    (hu : ∃ th hr', (∀ k τ, IsInfEmb τ.1 (th k τ)) ∧ DictIsUnif V dict Kf th hr')
    (hm : ∃ hr' : V.rank = r, ∀ k, ModelW V hr' (X k)) (hmu : MuUnit V dict mu) (hc : Continuous mu) :
    (∃ th, (∀ k τ, IsInfEmb τ.1 (th k τ)) ∧ DictIsUnif W (castDict hV dict) Kf' th hr) ∧
      (∀ k, ModelW W hr (X k)) ∧ MuUnit W (castDict hV dict) (castDict hV mu) ∧ Continuous (castDict hV mu) := by
  subst hV
  obtain rfl : Kf' = Kf := Subgroup.ext hK
  obtain ⟨th, hr', h1, h2⟩ := hu
  obtain ⟨hr'', h3⟩ := hm
  exact ⟨⟨th, h1, h2⟩, h3, hmu, hc⟩

theorem goodDict_core : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → R.IsModels → TieIn T R κ v₀ → T.pb = R.C.P.pb → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GoodEmb T.Q.c (res T σ) → ∀ hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i, ∀ w, WtIs (R.MW i σ) w → GoodDict R.θ (R.MW i σ) w (rank_Wc i) (T.U ((i : ℕ) + 1) (res T σ)).X (laU (T.U ((i : ℕ) + 1) (res T σ)) (wtA (κ i)) (κ i).n) (castDict hV (T.dict ((i : ℕ) + 1) (res T σ))) (castDict hV (T.mu ((i : ℕ) + 1) (res T σ))) (T.cE ((i : ℕ) + 1) (res T σ)) (levG (Wc D i) (R.βW i) (R.datWp i R.triv)) := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ hL hM h hpb i σ hσ hV w hw
  obtain ⟨hK, -, hfin, hopen⟩ := GlobalTheory.T.realisation_principalLevel_eq_coreLevel_open D G Pl0 T0 A T R κ v₀ hL hM h hpb i σ hσ hV
  have hj : InR D ((i : ℕ) + 1) := inR i
  obtain ⟨h1, h2, h3, h4⟩ := castDict_laws hV (rank_Wc i) _ _ (T.mu ((i : ℕ) + 1) (res T σ)) _ _ hK
    (h.laws.dictU _ hj _ hσ) (h.laws.modelW _ hj _ hσ) (h.laws.muUnit _ hj _ hσ) (h.laws.muCont _ hj _ hσ)
  have hc : ∀ k, ‖T.cE ((i : ℕ) + 1) (res T σ) k‖ = 1 := h.laws.cUnit _ hj _ hσ
  exact
    { inf := hM.inf
      base := GlobalTheory.T.base_frame_of_realization_models D G Pl0 T0 A T R κ v₀ hM h i σ hσ hV
      unif := h1
      model := h2
      muUnit := h3
      muCont := h4
      chi := h.laws.chiTriv _ hj _ hσ _ _ (dom_wtA (κ i))
      cNe := fun k h0 => by
        have := hc k
        rw [h0, norm_zero] at this
        exact zero_ne_one this
      cBdd := ⟨1, fun k => (hc k).le⟩
      fin := @Finite.of_fintype _ (T.U ((i : ℕ) + 1) (res T σ)).fin
      levFin := hfin
      levOpen := hopen
      muK := GlobalTheory.T.dictionaryChar_eq_one_on_principalLevel D G Pl0 T0 A T R κ v₀ hL hM h hpb i σ hσ hV
      wt := GlobalTheory.T.extremalWeight_eq_character_exponent_add D G Pl0 T0 A T R κ v₀ hM h i σ hσ hV w hw }

end GlobalTheory.HolDict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubeValuesIntegral
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ChTor GlobalTheory.HTLat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.WeilIntegral

theorem exists_smooth_chart {O : Type} [CommRing O] (X : Over (Sp O)) [Smooth X.hom] (W : X.left.Opens)
    (B : Type) [CommRing B] [Algebra O B] [IsLocalRing B] (w : specO O B ⟶ X) (hw : InOpen W w) :
    ∃ (R : Type) (_ : CommRing R) (_ : Algebra O R) (_ : Algebra.Smooth O R) (θ : R →ₐ[O] B)
      (r : specO O R ⟶ X), ptMap θ ≫ r = w ∧ InOpen W r := by
  let w₀ : Spec (CommRingCat.of B) ⟶ X.left := w.left
  have hx : w₀ (IsLocalRing.closedPoint B) ∈ W := by
    have : IsLocalRing.closedPoint B ∈ w₀ ⁻¹ᵁ W := by
      rw [show w₀ ⁻¹ᵁ W = ⊤ from hw]; trivial
    exact this
  obtain ⟨R, f, hf, h1, h2⟩ := Scheme.exists_affine_mem_range_and_range_subset hx
  have hr : Set.range w₀ ⊆ Set.range f := by
    have : w₀ ⁻¹ᵁ f.opensRange = ⊤ := Scheme.preimage_eq_top_of_closedPoint_mem w₀ h1
    rintro _ ⟨y, rfl⟩
    have hy : y ∈ w₀ ⁻¹ᵁ f.opensRange := by rw [this]; trivial
    exact hy
  let l := IsOpenImmersion.lift f w₀ hr
  have hl : l ≫ f = w₀ := IsOpenImmersion.lift_fac _ _ _
  let α : CommRingCat.of O ⟶ R := Spec.preimage (f ≫ X.hom)
  have hα : Spec.map α = f ≫ X.hom := Spec.map_preimage _
  letI : Algebra O R := α.hom.toAlgebra
  have hs : Smooth (Spec.map α) := by rw [hα]; infer_instance
  have hs' : α.hom.Smooth := (HasRingHomProperty.Spec_iff (P := @Smooth)).1 hs
  let β : R ⟶ CommRingCat.of B := Spec.preimage l
  have hβ : Spec.map β = l := Spec.map_preimage _
  have hc : α ≫ β = CommRingCat.ofHom (algebraMap O B) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hα, hβ, ← Category.assoc, hl]
    exact Over.w w
  let θ : R →ₐ[O] B := ⟨β.hom, fun a => congrArg (fun g => g.hom a) hc⟩
  refine ⟨R, inferInstance, inferInstance, hs', θ, Over.homMk f hα.symm, ?_, ?_⟩
  · ext1
    exact (congrArg (· ≫ f) hβ).trans hl
  · exact top_le_iff.1 fun y _ => h2 ⟨y, rfl⟩

theorem CubeIn.comp {S : Scheme.{0}} {X T T' : Over S} [GrpObj X] {U : X.left.Opens} {z a b c : T ⟶ X}
    (h : CubeIn U z a b c) (u : T' ⟶ T) : CubeIn U (u ≫ z) (u ≫ a) (u ≫ b) (u ≫ c) := by
  intro i j k hi hj hk
  have := (h i j k hi hj hk).comp u
  simpa only [MonObj.comp_mul, MonObj.comp_pow] using this

theorem exists_smooth_cube {O : Type} [CommRing O] (G : Over (Sp O)) [GrpObj G] [Smooth G.hom]
    (U : G.left.Opens) (B : Type) [CommRing B] [Algebra O B] [IsLocalRing B] (z a b c : specO O B ⟶ G)
    (h : CubeIn U z a b c) :
    ∃ (R : Type) (_ : CommRing R) (_ : Algebra O R) (_ : Algebra.Smooth O R) (θ : R →ₐ[O] B)
      (z₀ a₀ b₀ c₀ : specO O R ⟶ G), ptMap θ ≫ z₀ = z ∧ ptMap θ ≫ a₀ = a ∧ ptMap θ ≫ b₀ = b ∧
        ptMap θ ≫ c₀ = c ∧ CubeIn U z₀ a₀ b₀ c₀ := by
  have h2 : ∀ X Y : Over (Sp O), Smooth X.hom → Smooth Y.hom → Smooth (X ⊗ Y).hom := by
    intro X Y hX hY
    have : Smooth (pullback.fst X.hom Y.hom) :=
      smooth_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback X.hom Y.hom).flip hY
    exact inferInstanceAs (Smooth (pullback.fst X.hom Y.hom ≫ X.hom))
  let X : Over (Sp O) := (G ⊗ G) ⊗ (G ⊗ G)
  haveI : Smooth X.hom := h2 _ _ (h2 _ _ ‹_› ‹_›) (h2 _ _ ‹_› ‹_›)
  let p₁ : X ⟶ G := fst _ _ ≫ fst _ _
  let p₂ : X ⟶ G := fst _ _ ≫ snd _ _
  let p₃ : X ⟶ G := snd _ _ ≫ fst _ _
  let p₄ : X ⟶ G := snd _ _ ≫ snd _ _
  let w : specO O B ⟶ X := lift (lift z a) (lift b c)
  have e₁ : w ≫ p₁ = z := by simp [w, p₁]
  have e₂ : w ≫ p₂ = a := by simp [w, p₂]
  have e₃ : w ≫ p₃ = b := by simp [w, p₃]
  have e₄ : w ≫ p₄ = c := by simp [w, p₄]
  let V : ℕ × ℕ × ℕ → X.left.Opens := fun n => (p₁ * p₂ ^ n.1 * p₃ ^ n.2.1 * p₄ ^ n.2.2).left ⁻¹ᵁ U
  let s : Finset (ℕ × ℕ × ℕ) := Finset.Iic (1, 1, 1)
  have key : ∀ {T : Over (Sp O)} (r : T ⟶ X),
      InOpen (s.inf V) r ↔ CubeIn U (r ≫ p₁) (r ≫ p₂) (r ≫ p₃) (r ≫ p₄) := by
    intro T r
    have e : ∀ n : ℕ × ℕ × ℕ, InOpen (V n) r ↔
        InOpen U ((r ≫ p₁) * (r ≫ p₂) ^ n.1 * (r ≫ p₃) ^ n.2.1 * (r ≫ p₄) ^ n.2.2) := by
      intro n
      simp only [← MonObj.comp_pow, ← MonObj.comp_mul]
      unfold InOpen
      rw [Over.comp_left, Scheme.Hom.comp_preimage]
    constructor
    · intro hr i j k hi hj hk
      refine (e (i, j, k)).1 (top_le_iff.1 ?_)
      rw [← show r.left ⁻¹ᵁ s.inf V = ⊤ from hr]
      exact Scheme.Hom.preimage_mono _ (Finset.inf_le (by simp [s, hi, hj, hk]))
    · intro hr
      refine top_le_iff.1 fun y _ => ?_
      change r.left y ∈ ((s.inf V : X.left.Opens) : Set X.left)
      rw [TopologicalSpace.Opens.coe_finset_inf, Finset.inf_set_eq_iInter]
      refine Set.mem_iInter₂.2 fun n hn => ?_
      obtain ⟨h1, h2, h3⟩ := Finset.mem_Iic.1 hn
      have : y ∈ r.left ⁻¹ᵁ V n := by
        rw [show r.left ⁻¹ᵁ V n = ⊤ from (e n).2 (hr _ _ _ h1 h2 h3)]; trivial
      exact this
  obtain ⟨R, _, _, _, θ, r, hr, hW⟩ := exists_smooth_chart X (s.inf V) B w
    ((key w).2 (by rwa [e₁, e₂, e₃, e₄]))
  refine ⟨R, _, _, ‹_›, θ, r ≫ p₁, r ≫ p₂, r ≫ p₃, r ≫ p₄, ?_, ?_, ?_, ?_, (key r).1 hW⟩ <;>
    rw [← Category.assoc, hr] <;> assumption

def pushPt {S S' : Scheme.{0}} {A : Over S'} [GrpObj A] {G : Over S} [GrpObj G] {f : S' ⟶ S}
    {φ : A.left ⟶ G.left} (h : IsGrpPullback A G f φ) (T : Over S') :
    (T ⟶ A) →* (Over.mk (T.hom ≫ f) ⟶ G) :=
  MonoidHom.mk' (fun x => Over.homMk (x.left ≫ φ) (by
      change (x.left ≫ φ) ≫ G.hom = T.hom ≫ f
      rw [Category.assoc, h.1.w, ← Category.assoc, Over.w]))
    fun x y => Over.OverMorphism.ext (h.2 T x y _ _ rfl rfl).symm

theorem exists_generic_cube {S S' : Scheme.{0}} {A : Over S'} [GrpObj A] {G : Over S} [GrpObj G] {f : S' ⟶ S}
    {φ : A.left ⟶ G.left} (h : IsGrpPullback A G f φ) (T : Over S') (U : G.left.Opens)
    (z a b c : Over.mk (T.hom ≫ f) ⟶ G) (hc : CubeIn U z a b c) :
    ∃ z' a' b' c' : T ⟶ A, z'.left ≫ φ = z.left ∧ a'.left ≫ φ = a.left ∧ b'.left ≫ φ = b.left ∧
      c'.left ≫ φ = c.left ∧ CubeIn (φ ⁻¹ᵁ U) z' a' b' c' := by
  have hs : Function.Surjective (pushPt h T) := fun x =>
    ⟨Over.homMk (h.1.lift x.left T.hom (Over.w x)) (h.1.lift_snd _ _ _),
      Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩
  obtain ⟨z, rfl⟩ := hs z
  obtain ⟨a, rfl⟩ := hs a
  obtain ⟨b, rfl⟩ := hs b
  obtain ⟨c, rfl⟩ := hs c
  refine ⟨z, a, b, c, rfl, rfl, rfl, rfl, fun i j k hi hj hk => ?_⟩
  have := hc i j k hi hj hk
  simp only [← map_pow, ← map_mul] at this
  exact this

theorem exists_numerator {O C : Type} [CommRing O] [IsDomain O] [Field C] [Algebra O C] [IsFractionRing O C]
    (R : Type) [CommRing R] [Algebra O R] (s : (C ⊗[O] R)ˣ) :
    ∃ (f g : R) (c e : O), c ≠ 0 ∧ e ≠ 0 ∧ f * g = algebraMap O R c ∧
      (1 : C) ⊗ₜ[O] f = algebraMap O (C ⊗[O] R) e * s := by
  let m : R →ₗ[O] C ⊗[O] R := TensorProduct.mk O C R 1
  haveI : IsLocalizedModule (nonZeroDivisors O) m :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors O) C m).2 (TensorProduct.isBaseChange O R C)
  obtain ⟨⟨f, e₁⟩, hf⟩ := IsLocalizedModule.surj (nonZeroDivisors O) m (s : C ⊗[O] R)
  obtain ⟨⟨g, e₂⟩, hg⟩ := IsLocalizedModule.surj (nonZeroDivisors O) m (s⁻¹ : (C ⊗[O] R)ˣ)
  have hf' : (1 : C) ⊗ₜ[O] f = (e₁ : O) • (s : C ⊗[O] R) := hf.symm
  have hg' : (1 : C) ⊗ₜ[O] g = (e₂ : O) • ((s⁻¹ : (C ⊗[O] R)ˣ) : C ⊗[O] R) := hg.symm
  have h : m (f * g) = m (((e₁ : O) * e₂) • 1) := by
    have : m (f * g) = ((1 : C) ⊗ₜ[O] f) * ((1 : C) ⊗ₜ[O] g) := by simp [m]
    rw [this, hf', hg', smul_mul_smul_comm, Units.mul_inv, map_smul]
    rfl
  obtain ⟨e₃, h₃⟩ := IsLocalizedModule.exists_of_eq (S := nonZeroDivisors O) h
  have n := fun x : nonZeroDivisors O => nonZeroDivisors.coe_ne_zero x
  refine ⟨(e₃ : O) • f, g, e₃ * (e₁ * e₂), e₃ * e₁, mul_ne_zero (n _) (mul_ne_zero (n _) (n _)),
    mul_ne_zero (n _) (n _), ?_, ?_⟩
  · rw [smul_mul_assoc, Algebra.algebraMap_eq_smul_one, mul_smul]
    exact h₃
  · rw [TensorProduct.tmul_smul, hf', smul_smul, Algebra.smul_def]

theorem cubeValuesIntegral_of_localUnits {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0}
    {O : Type} [CommRing O] [Algebra O C] {Λ : Type} [CommRing Λ] [StarRing Λ] (P : Point p v O Λ)
    (hL : LocalUnits O) : CubeValuesIntegral P := by
  rintro U Θ hΘ B _ _ _ _ _ ⟨ψ₀⟩ z a b c hcube
  have hinj := P.integers.hom_inj
  haveI : IsDomain O := hinj.isDomain (algebraMap O C)
  haveI : IsFractionRing O C := P.integers.isFractionRing
  haveI : Smooth P.G.hom := P.semi.smooth
  obtain ⟨R, _, _, _, θ, z₀, a₀, b₀, c₀, rfl, rfl, rfl, rfl, h₀⟩ := exists_smooth_cube P.G U B z a b c hcube
  let iC : C →+* C ⊗[O] R := Algebra.TensorProduct.includeLeftRingHom
  let iR : R →+* C ⊗[O] R := (Algebra.TensorProduct.includeRight (R := O) (A := C) (B := R)).toRingHom
  let t : Sp (C ⊗[O] R) ⟶ Sp C := spMap iC
  let m : Over.mk ((Over.mk t).hom ≫ spMap (algebraMap O C)) ⟶ specO O R := Over.homMk (spMap iR) (by
    change spMap iR ≫ spMap (algebraMap O R) = spMap iC ≫ spMap (algebraMap O C)
    simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap.symm)
  obtain ⟨z₁, a₁, b₁, c₁, hz, ha, hb, hc, h₁⟩ :=
    exists_generic_cube P.gen_pull (Over.mk t) U _ _ _ _ (h₀.comp m)
  obtain ⟨f, g, k, e, hk, he, hfg, hf⟩ := exists_numerator R (Θ _ t z₁ a₁ b₁ c₁)
  obtain ⟨u, hu⟩ := hL R B θ ψ₀ f g k hk hfg
  have hd : ψ₀ (θ f) ≠ 0 := by
    have := congrArg (fun x => ψ₀ (θ x)) hfg
    simp only [map_mul, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply] at this
    exact left_ne_zero_of_mul (this ▸ hk)
  have he' : algebraMap O C e ≠ 0 := (map_ne_zero_iff _ hinj).2 he
  refine ⟨Units.mk0 (algebraMap O C (ψ₀ (θ f)) / algebraMap O C e)
    (div_ne_zero ((map_ne_zero_iff _ hinj).2 hd) he'), u, fun ψ z' a' b' c' hz' ha' hb' hc' => ?_⟩
  let φ : C ⊗[O] R →ₐ[O] C := Algebra.TensorProduct.lift (AlgHom.id O C)
    ((Algebra.ofId O C).comp (ψ.comp θ)) fun _ _ => Commute.all _ _
  have key : ∀ (x₀ : specO O R ⟶ P.G) (x₁ : Over.mk t ⟶ P.A.A) (x' : Pts P.A.A),
      x₁.left ≫ P.gen = (m ≫ x₀).left → IsGeneric P (ptMap ψ ≫ ptMap θ ≫ x₀) x' →
      x'.left = spMap φ.toRingHom ≫ x₁.left := by
    intro x₀ x₁ x' h h'
    refine P.gen_pull.1.hom_ext ?_ ?_
    · refine h'.trans ?_
      refine Eq.trans ?_ ((Category.assoc _ _ _).trans (congrArg (spMap φ.toRingHom ≫ ·) h)).symm
      change spMap (algebraMap O C) ≫ spMap ψ.toRingHom ≫ spMap θ.toRingHom ≫ x₀.left =
        spMap φ.toRingHom ≫ spMap iR ≫ x₀.left
      simp only [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 3
      ext x
      simp [φ, iR]
    · refine (Over.w x').trans ?_
      refine Eq.trans ?_ ((Category.assoc _ _ _).trans (congrArg (spMap φ.toRingHom ≫ ·) (Over.w x₁))).symm
      change 𝟙 (Sp C) = spMap φ.toRingHom ≫ spMap iC
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id]
      congr 1
      ext x
      simp [φ, iC]
  rw [hΘ _ _ φ.toRingHom t _ z₁ a₁ b₁ c₁ z' a' b' c' (key _ _ _ hz hz') (key _ _ _ ha ha') (key _ _ _ hb hb')
    (key _ _ _ hc hc') h₁]
  have h2 := congrArg φ hf
  rw [map_mul, AlgHom.commutes] at h2
  have h3 : φ ((1 : C) ⊗ₜ[O] f) = algebraMap O C (ψ (θ f)) := by simp [φ]
  have h4 : ψ (θ f) = ψ₀ (θ f) * ψ u := by
    conv_lhs => rw [hu]
    simp
  rw [h3, h4, map_mul] at h2
  change φ _ = _
  rw [Units.val_mk0, div_mul_eq_mul_div, h2, mul_div_cancel_left₀ _ he']

theorem cubeValuesIntegral (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C ℝ≥0) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C]
    (Λ : Type) [CommRing Λ] [StarRing Λ] (P : Point p v O Λ) : LocalUnits O → CubeValuesIntegral P :=
  cubeValuesIntegral_of_localUnits P

end GlobalTheory.WeilIntegral
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelLocReprContDiffOnTarget
section
open Set Matrix MeasureTheory Filter Topology
open GlobalTheory.HermFrame
open scoped ComplexOrder ContDiff ComplexConjugate

noncomputable section

namespace GlobalTheory.CxForm.HolAtlas

open GlobalTheory.GoodMetric (coordVec)

theorem del_loc_repr_contDiffOn : ∀ {M : Type} [TopologicalSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) (α : A.Fld), A.IsForm α → ∀ (i : A.ι) (S : Finset (Fin (n + n))), ContDiffOn ℝ ∞ (fun v => (GlobalTheory.CxForm.bas n).repr (A.loc (A.del α) i v) S) (A.e i).target := by
  intro M _ n A α hα i S
  have key : ∀ v ∈ (A.e i).target, (GlobalTheory.CxForm.bas n).repr (A.loc (A.del α) i v) S =
      ∑ a, ∑ T, GlobalTheory.del (fun x => (GlobalTheory.CxForm.bas n).repr (A.loc α i x) T) v (coordVec a) *
        (GlobalTheory.CxForm.bas n).repr (GlobalTheory.CxForm.dz a * GlobalTheory.CxForm.bas n T) S := by
    intro v hv
    have h1 : A.loc (A.del α) i v = GlobalTheory.CxForm.delAt (A.loc α i) v := by
      rw [GlobalTheory.CxForm.HolAtlas.loc, dif_pos hv]
      simp only [GlobalTheory.CxForm.HolAtlas.del, GlobalTheory.CxForm.HolAtlas.Pt.crd, GlobalTheory.CxForm.HolAtlas.Pt.ch, GlobalTheory.CxForm.HolAtlas.Pt.pt, (A.e i).right_inv hv]
    rw [h1, GlobalTheory.CxForm.delAt]
    simp only [GlobalTheory.CxForm.coefwise, Finset.mul_sum, mul_smul_comm, map_sum, map_smul,
      Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul]
  refine ContDiffOn.congr ?_ key
  have ho := (A.e i).open_target
  refine ContDiffOn.sum fun a _ => ContDiffOn.sum fun T _ => ContDiffOn.mul ?_ contDiffOn_const
  have hf := hα.smooth i T
  have hd := hf.fderiv_of_isOpen ho (m := ∞) (by simp)
  have h1 : ContDiffOn ℝ ∞ (fun v => fderiv ℝ (fun x => (GlobalTheory.CxForm.bas n).repr (A.loc α i x) T) v (coordVec a))
      (A.e i).target := hd.clm_apply contDiffOn_const
  have h2 : ContDiffOn ℝ ∞ (fun v => fderiv ℝ (fun x => (GlobalTheory.CxForm.bas n).repr (A.loc α i x) T) v
      (Complex.I • coordVec a)) (A.e i).target := hd.clm_apply contDiffOn_const
  refine ((h1.sub (h2.const_smul Complex.I)).const_smul (1 / 2 : ℂ)).congr fun v _ => ?_
  rfl

end GlobalTheory.CxForm.HolAtlas
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelMulOfDelEqZeroStatement
section
open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.del_mul_of_del_eq_zero' : ∀ {M : Type} [TopologicalSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) (α β : A.Fld), A.IsForm α → A.IsForm β → A.del β = 0 → A.del (α * β) = A.del α * β := by
  first | exact @GlobalTheory.CxForm.DelClosed.del_mul_of_del_eq_zero | exact GlobalTheory.CxForm.DelClosed.del_mul_of_del_eq_zero | (intros; apply GlobalTheory.CxForm.DelClosed.del_mul_of_del_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramesTildeGammaValuesStatement
section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows GlobalTheory.ColRows
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frames_tilde_gamma_values : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) [IsTotallyComplex D.what₂.LL] (T : Formalism.L2.TiedDataSK ex) (P : RowSideFamily ex) (K : SquareIntegrableColumnsCompatible T P), ColPins K → K.c.mu P.A3.fam3.base3.μ0 = 1 → ∀ X0, IsFrames (P.A3.side3 P.Ps P.ψs P.Zs) X0 → ∀ v F, ((Formalism.L2.Col.mtildeGSD K.c.W K.c.Ch K.c.sel (K.c.mu P.A3.fam3.base3.μ0) K.c.Lv).ipAt (K.c.hP P.A3.fam3.base3.μ0) v ((K.c.ev P.Zs P.A3.fam3.base3.μ0 F).1).1 ((K.c.ev P.Zs P.A3.fam3.base3.μ0 F).1).1).re ≤ Formalism.HermitianLatticesTheory.normAt (Pi.basisFun D.what₂.LL (Fin ((P.A3.side3 P.Ps P.ψs P.Zs).nV P.A3.fam3.base3.μ0))) X0 v F ^ 2 := by
  first | exact @GlobalTheory.ColEvNorm.ev_ipAt_le_normAt_sq | exact GlobalTheory.ColEvNorm.ev_ipAt_le_normAt_sq | (intros; apply GlobalTheory.ColEvNorm.ev_ipAt_le_normAt_sq <;> assumption)
end

