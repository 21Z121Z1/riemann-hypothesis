import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.CoefMemFlagSec
import Development.AutomorphicArithmetic.PrimeDiscriminants.SlopeTestRemainingChoices
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0017
import Formalism.LocalRingCardinality.Bundle0004
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.OEOsInjective
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs

-- bundled from Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.FlagSectionAction
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.FlagSectionAction

open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH
  Formalism.L2.Theta Formalism.L2.Pj
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {D : D7} (T : Core D)

def forms (j : ℕ) (w : WeightFamilies.Wt D j) : Submodule T.Q.c.F (T.R j) :=
  cusp (T.Q.Xo j) T.Q.c (T.U j) (wtA w) w.n

def values (j : ℕ) (la : HeightOneSpectrum (𝓞 T.Q.c.F)) : Set (T.R j → EReal) :=
  valSet (T.Q.Xo j) T.Q.c (algCls (T.Q.Xo j) T.Q.c) la

theorem isVal_values (j : ℕ) (la : HeightOneSpectrum (𝓞 T.Q.c.F)) : ∀ v ∈ values T j la, IsVal la v :=
  isVal_valSet la

open Classical in

def good (σ : T.Q.c.F →+* ℂ) : T.Q.c.F →+* ℂ :=
  if GoodEmb T.Q.c σ then σ else (starRingEnd ℂ).comp σ

theorem goodEmb_good (σ : T.Q.c.F →+* ℂ) : GoodEmb T.Q.c (good T σ) := goodEmb_goodOf T.Q.c σ

def supGood (j : ℕ) (w : WeightFamilies.Wt D j) (σ : T.Q.c.F →+* ℂ) (f : T.R j) : ℝ :=
  lieFac (T.Q.Dw j) (xiR D) (wtA w) *
    (supE (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) (rdU (T.U j σ) f)).toReal

def petGood (j : ℕ) (w : WeightFamilies.Wt D j) (σ : T.Q.c.F →+* ℂ) (f : T.R j) : ℝ :=
  (eLpNorm (onQ (T.V j σ) (T.phiAd j σ (wtA w) f)) 2 (muQ1 (T.V j σ))).toReal

def supNorm (j : ℕ) (w : WeightFamilies.Wt D j) (σ : T.Q.c.F →+* ℂ) (f : T.R j) : ℝ := supGood T j w (good T σ) f

def petNorm (j : ℕ) (w : WeightFamilies.Wt D j) (σ : T.Q.c.F →+* ℂ) (f : T.R j) : ℝ := petGood T j w (good T σ) f

def Cusps (j : ℕ) : Type := Σ k : (T.U j T.σ₀).Comp, FJ.CuspFD ((T.U j T.σ₀).X k) (WeightFamilies.rho D j)

def charLat (j : ℕ) (cu : Cusps T j) : Submodule (𝓞 D.host.E) (Fin (WeightFamilies.rho D j) → D.host.E) :=
  FJ.XcFD 1 cu.2

theorem charLat_isLattice (j : ℕ) (cu : Cusps T j) : Submodule.IsLattice D.host.E (charLat T j cu) :=
  FJ.xcFD_lat 1 (fun h => one_ne_zero (α := D.host.E)
    ((FractionalIdeal.mem_zero_iff _).1 (h ▸ FractionalIdeal.one_mem_one _))) cu.2

abbrev domSec (j : ℕ) (cu : Cusps T j) (w : WeightFamilies.Wt D j) : Type :=
  flagSec T.σ₀ ((T.U j T.σ₀).X cu.1) (laU (T.U j T.σ₀) (wtA w) w.n cu.1)

variable {T}

theorem isFlagSec_rd (h : LawsM T) {j : ℕ} (hj : InR D j) (w : WeightFamilies.Wt D j) (f : forms T j w) (k) :
    IsFlagSec ((T.U j T.σ₀).X k) (laU (T.U j T.σ₀) (wtA w) w.n k) (rdU (T.U j T.σ₀) f.1 k) :=
  have h1 := (h.unf j hj T.σ₀ T.good_σ₀).2.2.2.2.1 (wtA w) w.n (dom_wtA w) f.1 (cusp_le_sec _ _ _ _ _ f.2) k
  ⟨h1.1, h1.2.1⟩

theorem orbInt (h : LawsCore T) {j : ℕ} (hj : InR D j) (w : WeightFamilies.Wt D j) :
    FJ.RdOrbInt T.σ₀ (T.X₀ j) (WeightFamilies.rho D j) ((rdU (T.U j T.σ₀)).comp (forms T j w).subtype) :=
  FJ.rdOrbInt_of_latZ _ _ _ (fun f k => (isFlagSec_rd h.toLawsM hj w f k).1.continuousOn) (h.latZ j hj)

def coefIn (h : LawsCore T) {j : ℕ} (hj : InR D j) (cu : Cusps T j)
    (χ : Matrix (Fin (WeightFamilies.rho D j)) (Fin (WeightFamilies.rho D j)) D.host.E) (w : WeightFamilies.Wt D j) :
    forms T j w →ₗ[T.Q.c.F] domSec T j cu w :=
  (FJ.sgF T.σ₀ (T.X₀ j) ((rdU (T.U j T.σ₀)).comp (forms T j w).subtype) (orbInt h hj w) cu χ).codRestrict _
    fun f => coef_mem_flagSec T.σ₀ _ _ cu.2 (FJ.orbDom_of_latZ _ (h.latZ j hj) cu) _ ⟨_, orbInt h hj w f cu⟩
      (isFlagSec_rd h.toLawsM hj w f cu.1)

open Classical in

def coef (h : LawsCore T) (j : ℕ) (cu : Cusps T j) (χ : WeightFamilies.ExpoSet D (charLat T j cu)) (w : WeightFamilies.Wt D j) :
    forms T j w →ₗ[T.Q.c.F] domSec T j cu w :=
  if hj : InR D j then coefIn h hj cu χ.1 w else 0

theorem petGood_eq {j : ℕ} (w : WeightFamilies.Wt D j) (σ : T.Q.c.F →+* ℂ)
    (hm : JMemL2 (T.V j σ) σ (rdC (T.U j) σ (wtA w) w.n) (T.dict j σ) (T.mu j σ)) {f : T.R j} (hf : f ∈ forms T j w) :
    petGood T j w σ f = l2C (T.U j) σ (T.V j σ) (T.dict j σ) (T.mu j σ) (xiR D) (wtA w) w.n hm f := by
  have hf' : f ∈ cusp (T.Q.Xo j) T.Q.c (T.U j) (wtA w) w.n := hf
  rw [l2C, dif_pos hf', petGood, Core.phiAd, map_smul, eLpNorm_const_smul, ENNReal.toReal_mul]
  congr 1
  · simp [abs_of_pos (lieFac_pos _ _ _)]
  · exact (Lp.norm_toLp _ (hm ⟨f, hf'⟩)).symm

theorem isNormOn_supNorm (h : LawsM T) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j) (σ : T.Q.c.F →+* ℂ) :
    IsNormOn (forms T j w) σ (supNorm T j w σ) :=
  (isNormOn_supC (xiR D) (h.supDef j hj) (dom_wtA w) (goodEmb_good T σ)).of_goodOf

theorem isNormOn_petNorm (h : LawsM T) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j) (σ : T.Q.c.F →+* ℂ) :
    IsNormOn (forms T j w) σ (petNorm T j w σ) := by
  have hσ := goodEmb_good T σ
  have h0 := (isNormOn_l2C (xiR D) (h.l2Def j hj _ hσ) (dom_wtA w)).of_goodOf
  have e : ∀ f ∈ forms T j w, petNorm T j w σ f = _ :=
    fun f hf => petGood_eq w _ (h.cuspidalL2Subspace j hj _ hσ _ _ (dom_wtA w)) hf
  refine ⟨fun f hf => ?_, fun f hf h1 => ?_, fun a f hf => ?_, fun f hf g hg => ?_⟩
  · rw [e f hf]; exact h0.nonneg f hf
  · rw [e f hf] at h1; exact h0.defin f hf h1
  · rw [e f hf, e _ (Submodule.smul_mem _ a hf)]; exact h0.smul a f hf
  · rw [e f hf, e g hg, e _ (Submodule.add_mem _ hf hg)]; exact h0.add f hf g hg

theorem petNorm_le_supNorm (h : LawsM T) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j) (σ : T.Q.c.F →+* ℂ) :
    ∀ f ∈ forms T j w, petNorm T j w σ f ≤ supNorm T j w σ f := by
  intro f hf
  have hσ := goodEmb_good T σ
  obtain ⟨th, hr, -, hd⟩ := h.dictU j hj _ hσ
  rw [petNorm, petGood_eq w _ (h.cuspidalL2Subspace j hj _ hσ _ _ (dom_wtA w)) hf]
  exact l2C_le_supC (xiR D) hσ _ hd.2.2.2.1 (h.muUnit j hj _ hσ) f hf

def record (h : LawsCore T) : WeightFamilies.Prov D :=
  mkB T.Q.eO (forms T) (fun j hj w => h.cuspFD j hj _ _ (dom_wtA w)) (values T) (isVal_values T)
    (supNorm T) (petNorm T) (isNormOn_supNorm h.toLawsM) (isNormOn_petNorm h.toLawsM) (petNorm_le_supNorm h.toLawsM)
    (Cusps T) (charLat T) (charLat_isLattice T) (fun j cu _ w => domSec T j cu w) (coef h)

variable (T)

def CuspsMaximal (j : ℕ) : Prop :=
  ∀ k : (T.U j T.σ₀).Comp, IsEmpty (FJ.CuspFD ((T.U j T.σ₀).X k) (WeightFamilies.rho D j + 1))

def ReadingInjective (j : ℕ) : Prop :=
  ∀ (w : WeightFamilies.Wt D j) (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ → ∀ (n : ℕ) (b : Fin n → forms T j w),
    LinearIndependent T.Q.c.F b → LinearIndependent ℂ fun i => rdU (T.U j σ) (b i).1

def ExponentsMatch (j : ℕ) : Prop :=
  ∀ (cu : Cusps T j) (χ : Matrix (Fin (WeightFamilies.rho D j)) (Fin (WeightFamilies.rho D j)) D.host.E), WeightFamilies.IsHerm D χ →
    ((∀ β ∈ FJ.zGam ((T.U j T.σ₀).X cu.1) cu.2, ∃ n : ℤ, FJ.prE ((T.U j T.σ₀).X cu.1) χ β = n) ↔
      WeightFamilies.IntOn D (charLat T j cu) χ ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E))

end GlobalTheory.IndefiniteRowSideFullHecke.FlagSectionAction
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.HalfDepthValuations
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.HalfDepthValuations

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.MainNotions.DIV.Cons

variable {D : D7}

def halfE (Q : Par D) (i : Fin 2) : Ideal (𝓞 D.host.E) :=
  Q.l.Mb ⊔ Ideal.span {((D.host.g i : ℕ) : 𝓞 D.host.E)}

def halfK (Q : Par D) (i : Fin 2) : Ideal (𝓞 D.host.K) :=
  (halfE Q i).comap (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))

def piGBar (X : ErrX D) (i : Fin 2) : 𝓞 D.host.E := barE D (X.piG i)

open Classical in

def piOf (Q : Par D) (X : ErrX D) (i : Fin 2) : 𝓞 D.host.E :=
  if piGBar X i ∈ halfE Q i then piGBar X i else X.piG i

open Classical in

def vdOf (D : D7) (p : ℕ) : ℝ :=
  if p ∈ D.host.small then D.host.vdH p
  else if p = D.host.q ∨ p = D.host.d then 1 / 2 else 0

def vdDiff (D : D7) (p : ℕ) : ℝ :=
  (padicValInt p (NumberField.discr D.host.E) : ℝ) / (Module.finrank ℚ D.host.E : ℝ)

def pageAt (D : D7) (T : ℕ) : DepPage where
  T := T
  g1 := D.host.g 0
  g2 := D.host.g 1
  q1 := D.host.q
  dd := D.host.d
  sm := D.host.small
  f := D.R.f
  r := D.R.r
  vd := vdOf D

def pageOf {L : SizeData₂ D} {P : ParameterChoice' D L} (PT : ParamsT D L P) : DepPage := pageAt D PT.TO

def depAt (Q : Par D) (X : ErrX D) (T : ℕ) (ka wL wF : ∀ j, WeightFamilies.Wt D j) : DepData D.host.E where
  Q := pageAt D T
  aL j := wtA (wL j)
  aF j := wtA (wF j)
  nW j := (wL j).n
  Dp j := ∑ τ, ∑ i, (ka j).aP τ i
  Dm j := ∑ τ, ∑ i, (ka j).aM τ i
  pi := piOf Q X

section Rec

variable {L : SizeData₂ D} {P : ParameterChoice' D L}

def depOf (Q : Par D) (X : ErrX D) (PT : ParamsT D L P) (hK : DV.KapDef D) : DepData D.host.E :=
  depAt Q X PT.TO (kaR PT hK) (lR PT hK) (fR PT hK)

def depCore (T : Core D) (X : ErrX D) (PT : ParamsT D L P) (hK : DV.KapDef D) : DepData D.host.E :=
  depOf T.Q X PT hK

end Rec

def Orient (Q : Par D) (X : ErrX D) : Prop := ∀ i, halfE Q i = Ideal.span {piGBar X i}

def OrientCore (T : Core D) (X : ErrX D) : Prop := Orient T.Q X

def PiGenSt (D : D7) : Prop :=
  ∀ (Q : Par D) (X : ErrX D), Q.PinHost → Q.PinLevel → ∀ i,
    Ideal.span {piOf Q X i} = halfE Q i ∧ (halfK Q i).IsMaximal ∧
      (halfK Q i).map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) = halfE Q i ∧
      (X.piG i ∈ halfE Q i ↔ piGBar X i ∉ halfE Q i)

def PiHalfSt (D : D7) : Prop :=
  ∀ (Q : Par D) (X : ErrX D), Q.PinHost → Q.PinLevel →
    ∀ (T : ℕ) (ka wL wF : ∀ j, WeightFamilies.Wt D j), PiHalf Q.l (depAt Q X T ka wL wF)

def HalfCoreSt (D : D7) : Prop :=
  ∀ T : Core D, LawsM T → ∀ i, halfK T.Q i = (T.pb i).asIdeal

def VdSt (D : D7) : Prop := ∀ p : ℕ, p.Prime → vdOf D p = vdDiff D p

theorem bar_eq_barE (Q : Par D) (a : 𝓞 D.host.E) : Q.H.bar a = barE D a := by
  apply IsFractionRing.injective (𝓞 D.host.E) D.host.E
  exact Q.H.bar_eq a

end GlobalTheory.IndefiniteRowSideFullHecke.HalfDepthValuations
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.HalfLevelCoefficients
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.HalfLevelCoefficients

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

structure IsHalf (D : D7) (Mb : Ideal (𝓞 D.host.E)) : Prop where
  fromK : Mb = Ideal.span {a | a ∈ Mb ∧ a ∈ Algebra.adjoin ℤ {w0E D}}
  prod : Mb * Mb.map (bH D) = Ideal.span {((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E)}
  coprime : Mb ⊔ Mb.map (bH D) = ⊤

theorem isHalf_levelG (D : D7) : IsHalf D (MbOf D [D.host.g 0, D.host.g 1]) where
  fromK := MbOf_fromK D _
  prod := by simpa [MbProdLaw] using MbProd_of D _ (splitG D)
  coprime := MbCop_of D _ (splitG D)

theorem three_le_g (D : D7) (k : Fin 2) : 3 ≤ D.host.g k := by
  have := (D.host.g_prime k).two_le
  have := g_ne_two D k
  omega

def levelAt (D : D7) (Mb : Ideal (𝓞 D.host.E)) (h : IsHalf D Mb) : Level (hostOfRecord D) where
  M := D.host.g 0 * D.host.g 1
  three_le := by
    have := three_le_g D 0
    have := three_le_g D 1
    nlinarith
  odd := ((D.host.g_prime 0).odd_of_ne_two (g_ne_two D 0)).mul ((D.host.g_prime 1).odd_of_ne_two (g_ne_two D 1))
  Mb := Mb
  fromK := h.fromK
  prod := h.prod
  coprime := h.coprime
  A := 1
  A_pos := Nat.one_pos

def coeffAt (D : D7) (hz : OZeta D) (Mb : Ideal (𝓞 D.host.E)) (h : IsHalf D Mb) : Coeff (levelAt D Mb h) where
  F := FO D
  fin := inferInstance
  conj τ a := conj_mem_FO D τ a
  zeta_mem := by
    obtain ⟨y, hy⟩ := hz
    have : (levelAt D Mb h).M' = D.host.g 0 * D.host.g 1 := by
      simp [Level.M', levelAt]
    rw [this, ← hy]
    exact phiO_mem_FO D y
  le := by
    rw [KA, IntermediateField.adjoin_le_iff, Set.insert_subset_iff, Set.singleton_subset_iff]
    refine ⟨phi0_mem_coeff_field D D.host.sqrtMinusD, ?_⟩
    have : (levelAt D Mb h).A = 1 := rfl
    rw [this, zeta_one]
    exact one_mem _

open Classical in

def datAt (D : D7) (j : ℕ) : Datum (hostOfRecord D) :=
  if hj : InR D j then datumW D j hj else datumW D 1 (inR_one D)

theorem datAt_rank_pos (D : D7) (j : ℕ) : 1 ≤ (datAt D j).p + (datAt D j).q := by
  have := D.R.m_add_three_le_k
  unfold datAt
  split_ifs with hj
  · show 1 ≤ (D.R.sigW j).1 + (D.R.sigW j).2
    simp only [Ranks.sigW]
    have := hj.1
    omega
  · show 1 ≤ (D.R.sigW 1).1 + (D.R.sigW 1).2
    simp only [Ranks.sigW]
    omega

def parWith (D : D7) (hF : OFull D) (hz : OZeta D) (Mb : Ideal (𝓞 D.host.E)) (h : IsHalf D Mb)
    (Xo : ∀ j, Moduli (datAt D j) (levelAt D Mb h)) : Par D where
  H := hostOfRecord D
  l := levelAt D Mb h
  c := coeffAt D hz Mb h
  Dw := datAt D
  Xo := Xo
  eO := eOf D hF

def parAt (D : D7) (hF : OFull D) (hz : OZeta D) (hN : N1ab) (Mb : Ideal (𝓞 D.host.E)) (h : IsHalf D Mb) : Par D :=
  parWith D hF hz Mb h fun j =>
    Classical.choice (hN D.host.E (hostOfRecord D) (datAt D j) (levelAt D Mb h) (datAt_rank_pos D j))

def IsParAt (D : D7) (Mb : Ideal (𝓞 D.host.E)) (Q : Par D) : Prop :=
  Q.Pins ∧ Q.l.Mb = Mb ∧ ∀ j, 1 ≤ (Q.Dw j).p + (Q.Dw j).q

def PrimesOver (D : D7) (pb : Fin 2 → HeightOneSpectrum (𝓞 D.host.K)) : Prop :=
  ∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ (pb k).asIdeal

def halfOf (D : D7) (pb : Fin 2 → HeightOneSpectrum (𝓞 D.host.K)) : Ideal (𝓞 D.host.E) :=
  ∏ k, (pb k).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))

def HalfOfPrimes (D : D7) : Prop :=
  ∀ pb : Fin 2 → HeightOneSpectrum (𝓞 D.host.K), PrimesOver D pb → IsHalf D (halfOf D pb)

theorem halfOfPrimes_iff (D : D7) : HalfOfPrimes D ↔
    ∀ pb : Fin 2 → HeightOneSpectrum (𝓞 D.host.K), PrimesOver D pb →
      ∃ l : Level (hostOfRecord D), l.M = D.host.g 0 * D.host.g 1 ∧ l.A = 1 ∧ l.Mb = halfOf D pb := by
  refine forall₂_congr fun pb _ => ⟨fun h => ⟨levelAt D _ h, rfl, rfl, rfl⟩, ?_⟩
  rintro ⟨l, hM, -, hb⟩
  rw [← hb]
  exact ⟨l.fromK, hM ▸ l.prod, l.coprime⟩

theorem isParAt_parWith (D : D7) (hF : OFull D) (hz : OZeta D) (Mb : Ideal (𝓞 D.host.E)) (h : IsHalf D Mb)
    (Xo : ∀ j, Moduli (datAt D j) (levelAt D Mb h)) : IsParAt D Mb (parWith D hF hz Mb h Xo) := by
  refine ⟨⟨⟨rfl, rfl, rfl, tauEmb_sqrt D⟩, ⟨rfl, rfl⟩, eOf_spec D hF, fun j hj => ?_⟩, rfl, datAt_rank_pos D⟩
  show IsDatW D j (datAt D j)
  unfold datAt
  rw [dif_pos hj]
  unfold datumW datumOfRecord
  exact isDatW_datumOf D _ j _ _

theorem isParAt_parAt (D : D7) (hF : OFull D) (hz : OZeta D) (hN : N1ab) (Mb : Ideal (𝓞 D.host.E))
    (h : IsHalf D Mb) : IsParAt D Mb (parAt D hF hz hN Mb h) :=
  isParAt_parWith D hF hz Mb h _

end GlobalTheory.IndefiniteRowSideFullHecke.HalfLevelCoefficients
end
end

