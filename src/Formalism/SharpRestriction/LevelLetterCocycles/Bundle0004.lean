import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoDuality
section
noncomputable section

namespace Formalism.MainNotions.BlochKatoDuality

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Module

section Rep

variable {G : Type} [Group G] {LL : Type} [Field LL]

def IsSubSumOf {W A B : Type} [AddCommGroup W] [Module LL W] [AddCommGroup A] [Module LL A]
    [AddCommGroup B] [Module LL B] (ρW : Representation LL G W) (ρA : Representation LL G A)
    (ρB : Representation LL G B) : Prop :=
  ∃ (a b : ℕ) (p : Fin a → W →ₗ[LL] A) (q : Fin b → W →ₗ[LL] B),
    (∀ i g w, p i (ρW g w) = ρA g (p i w)) ∧ (∀ j g w, q j (ρW g w) = ρB g (q j w)) ∧
    ∀ w, (∀ i, p i w = 0) → (∀ j, q j w = 0) → w = 0

end Rep

section Push

variable {G : Type} [Group G] [TopologicalSpace G] {Qp : Type} [Field Qp]
    {LL : Type} [Field LL] [Algebra Qp LL] {O : Type} [CommRing O] [Algebra O LL]
    {X : Type} [AddCommGroup X] [Module LL X] [Module Qp X] [IsScalarTower Qp LL X]
    [Module O X] [IsScalarTower O LL X] {ρX : Representation LL G X}
    {U : Type} [AddCommGroup U] [Module LL U] [Module Qp U] [IsScalarTower Qp LL U]
    [Module O U] [IsScalarTower O LL U] {ρU : Representation LL G U}
    [TopologicalSpace X] [ContinuousAdd X] [ContinuousConstSMul LL X]

def IsGMapD (LY : Lattice (O := O) ρX) (LT : Lattice (O := O) ρU) (φ : ↥LY.T →ₗ[O] (U ⧸ LT.T)) :
    Prop :=
  ∀ g y, φ (actT LY g y) = repD LT g (φ y)

def pushD (LY : Lattice (O := O) ρX) (LT : Lattice (O := O) ρU) (φ : ↥LY.T →ₗ[O] (U ⧸ LT.T))
    (y : ↥(latticeCocycles LY)) : G → U ⧸ LT.T :=
  fun g => φ (evT LY g y)

end Push

section Stmts

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] {O : Type} [CommRing O] [Algebra O LL]

def LiftAll (A Bt : GRep G Qp LL O) (e : ℕ) : Prop :=
  ∀ W₁ W₂ : GRep G Qp LL O, IsSubSumOf W₁.ρ A.ρ Bt.ρ → IsSubSumOf W₂.ρ A.ρ Bt.ρ →
    ∀ (L₁ : Lattice (O := O) W₁.ρ) (L₂ : Lattice (O := O) W₂.ρ) (F : LatHom L₁ L₂),
      F.Onto → F.LiftF PD e

def spanPush (X U : GRep G Qp LL O) (LT : Lattice (O := O) U.ρ) : Submodule O (G → U.V ⧸ LT.T) :=
  Submodule.span O {c | ∃ (LY : Lattice (O := O) X.ρ) (φ : ↥LY.T →ₗ[O] (U.V ⧸ LT.T))
    (_ : IsGMapD LY LT φ) (y : ↥(latticeCocycles LY)), (y : G → X.V) ∈ latticeFiniteCocycles PD LY ∧ c = pushD LY LT φ y}

def lenMod {M : Type} [AddCommGroup M] [Module O M] (S H : Submodule O M) : ℕ∞ :=
  Module.length O (↥(S ⊔ H) ⧸ H.comap (S ⊔ H).subtype)

end Stmts

section Main

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] [TopologicalSpace Qp]
    (PD : PeriodData G Qp K₀ K B BdR)

def Hyp {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] {O : Type} [CommRing O]
    [Algebra O LL] (V X U X' U' : GRep G Qp LL O) (χ : G →* LLˣ)
    (PX : X.V →ₗ[LL] X'.V →ₗ[LL] LL) (PU : U.V →ₗ[LL] U'.V →ₗ[LL] LL)
    (LT : Lattice (O := O) U.ρ) (LT' : Lattice (O := O) U'.ρ) (e : ℕ) : Prop :=
  IsTwistRep χ⁻¹ V.ρ X.ρ ∧ IsDR PD U.ρ ∧ IsDual1 PD X.ρ X'.ρ PX ∧
    IsDualLat1 PD LT LT' PU ∧ (LiftAll PD X U e ∨ (IsDR PD X.ρ ∧ LiftAll PD X' U' e))

def ArcTheoremGlobal : Prop :=
  ∀ (LL : Type) [Field LL] [Algebra Qp LL] [TopologicalSpace LL] (O : Type) [CommRing O]
    [Algebra O LL], GoodO (Qp := Qp) LL O →
  ∀ (V X U X' U' : GRep G Qp LL O) (χ : G →* LLˣ) (PX : X.V →ₗ[LL] X'.V →ₗ[LL] LL)
    (PU : U.V →ₗ[LL] U'.V →ₗ[LL] LL) (LT : Lattice (O := O) U.ρ) (LT' : Lattice (O := O) U'.ρ)
    (e : ℕ), Hyp PD V X U X' U' χ PX PU LT LT' e →
  ∀ (LY : Lattice (O := O) X.ρ) (φ : ↥LY.T →ₗ[O] (U.V ⧸ LT.T)), IsGMapD LY LT φ →
  ∀ y : ↥(latticeCocycles LY), (y : G → X.V) ∈ latticeFiniteCocycles PD LY →
    ((PD.p : O) ^ e) • pushD LY LT φ y ∈ HfD PD LT

def PushoutSpanLengthBound : Prop :=
  ∀ (LL : Type) [Field LL] [Algebra Qp LL] [TopologicalSpace LL] (O : Type) [CommRing O]
    [Algebra O LL], GoodO (Qp := Qp) LL O →
  ∀ (V X U X' U' : GRep G Qp LL O) (χ : G →* LLˣ) (PX : X.V →ₗ[LL] X'.V →ₗ[LL] LL)
    (PU : U.V →ₗ[LL] U'.V →ₗ[LL] LL) (LT : Lattice (O := O) U.ρ) (LT' : Lattice (O := O) U'.ρ)
    (e : ℕ), Hyp PD V X U X' U' χ PX PU LT LT' e →
  ∃ m k : ℕ, lenMod (spanPush PD X U LT) (HfD PD LT) = m ∧ lenOl PD (O := O) = k ∧
    m ≤ e * (finrank O ↥(latticeFiniteCohomology PD LT') + finrank O ↥LT.T) * k

end Main

section Bridge

variable {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]

def grepOf (T : Formalism.BasicNotions.LocLat G Qp LL O) : GRep G Qp LL O :=
  @GRep.mk G _ _ Qp LL O _ _ _ _ _ _ T.V T.acg T.modLL T.modQp T.towQp T.modO T.towO T.fdim T.top
    T.mtop T.cadd T.csmul T.ρ T.cont

def latOf (T : Formalism.BasicNotions.LocLat G Qp LL O) : Lattice (O := O) (grepOf T).ρ := T.L

end Bridge

section Packet

open Formalism.BasicNotions

def Conclusion1 (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : Loc.FinExt l), ArcTheoremGlobal ((D.loc l).PD K)

def Conclusion2 (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : Loc.FinExt l), PushoutSpanLengthBound ((D.loc l).PD K)

def adm1 (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : Loc.FinExt l), bkACore ((D.loc l).PD K)

def adm2 (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : Loc.FinExt l), bkBCore ((D.loc l).PD K)

def adm3 (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : Loc.FinExt l), LocalTateTopDegree ((D.loc l).PD K)

def ArchimedeanSignatureMatching (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : Loc.FinExt l), cycIntCore ((D.loc l).PD K)

def adm5 (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : Loc.FinExt l), TateFiniteness ((D.loc l).PD K)

def adm6 (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : Loc.FinExt l), drDualCore ((D.loc l).PD K)

def admitted (D : Formalism.BasicNotions.D7) : Prop :=
  adm1 D ∧ adm2 D ∧ adm3 D ∧ ArchimedeanSignatureMatching D ∧ adm5 D ∧ adm6 D

def Stmt (D : Formalism.BasicNotions.D7) : Prop := admitted D → Conclusion1 D ∧ Conclusion2 D

end Packet

end Formalism.MainNotions.BlochKatoDuality
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.FontExAll
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

def FontExAll (D : D7) (HW : HWOf D.loc) (_F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (hG : Good K s LL)
    (T₀ T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L),
    IsSESLat (Qp := ℚ_[l]) ι π →
    Function.Injective (((HW l).W K s LL hG).map ι) ∧ Function.Surjective (((HW l).W K s LL hG).map π) ∧
      ∀ x, ((HW l).W K s LL hG).map π x = 0 ↔ ∃ y, ((HW l).W K s LL hG).map ι y = x

end Formalism.MainNotions.N.Ln34

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.LocsCoverTw
section
noncomputable section

namespace Formalism.MainNotions.N

def LocsCoverTw (D : Formalism.BasicNotions.D7) : Prop := ∀ j' w', 1 ≤ j' → j' ≤ D.R.m → D.what₂.muAt w' ≠ D.what₂.mu0 →
  ∑ i ∈ D.nd.locs j' w', Module.finrank (D.nd.O i) (D.nd.Mt i) =
    Module.finrank D.what₂.LL (D.what₂.MtL (D.what₂.muTw w') j')

theorem locsCoverTw_of (D : Formalism.BasicNotions.D7) (h : D.nd.LocsCover) : LocsCoverTw D := by
  exact h

end Formalism.MainNotions.N

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.QpowOfTw
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions

namespace Formalism.MainNotions.N

def WildTriv : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ), l.Prime →
    ∀ (v : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A v → v ∉ placesOver E l →
    ∀ (M : Type) [Group M] (φ : G E Ω →* M), IsOpen (φ.ker : Set (G E Ω)) → (∀ g, ∃ n : ℕ, φ g ^ (l ^ n) = 1) →
    ∀ σ : G E Ω, (∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) → φ σ = 1

theorem qpow_of_tw (hW : WildTriv) (D : D7) (i : D.nd.Loc) :
    ∀ v ∈ D.nd.Q i, ∀ g ∈ Ine (F := D.host.E) (D.nd.plOm.1 v),
      ∃ n : ℕ, D.nd.chi i 1 g = D.nd.chi i 1 (D.nd.gam0 i v) ^ n := by
  classical
  intro v hv g hg
  have hS : v ∉ D.nd.S i := fun h => Finset.disjoint_left.1 (D.nd.SQ_disj i) h hv
  have hl : v ∉ placesOver D.host.E (D.nd.l i) := D.nd.SQ_l i v (Or.inr hv)
  have hgk : ∀ k, v ∉ placesOver D.host.E (D.host.g k) := by
    intro k hk
    apply hS
    rw [D.nd.S_def i v]
    refine ⟨?_, hl⟩
    fin_cases k
    · exact Or.inl hk
    · exact Or.inr (Or.inl hk)
  have hpd : v ∉ D.ntw.pD (D.ntw.twOf i) := by
    intro hp
    have h' : v ∈ ((D.ntw.pD (D.ntw.twOf i) : Finset _) : Set (HeightOneSpectrum (𝓞 D.host.E))) := hp
    rw [D.ntw.pD_eq, D.ntw.twOf_l] at h'
    exact hS ((D.nd.S_def i v).2 ⟨Or.inr (Or.inr h'), hl⟩)
  have hl' : v ∉ placesOver D.host.E (D.ntw.l (D.ntw.twOf i)) := by
    rw [D.ntw.twOf_l]
    exact hl
  have hchi : ∀ h ∈ Ine (F := D.host.E) (D.nd.plOm.1 v), D.nd.chi i 1 h = D.ntw.psiL i h := by
    intro h hh
    have h1 := D.ntw.twistCharacterFamily_unramified (D.ntw.twOf i) (D.nd.j i) (D.ntw.twSide i) v hl' hgk hpd (D.nd.plOm.1 v)
      (D.nd.plOm.2 v) h hh
    rw [D.ntw.chi_tw i, MonoidHom.mul_apply, MonoidHom.comp_apply, h1, map_one, one_mul]
  rw [hchi g hg, hchi _ (D.nd.locNd_chebotarevPlace_mem i v)]
  obtain ⟨m, hm⟩ := D.ntw.psiL_ord i (D.nd.gam0 i v)
  have hL : 1 ≤ D.nd.l i ^ m := Nat.one_le_pow _ _ (Fact.out : (D.nd.l i).Prime).pos
  let H : Subgroup (G D.host.E D.nd.Om) :=
    { carrier := {x | ∃ n : ℕ, D.ntw.psiL i x = D.ntw.psiL i (D.nd.gam0 i v) ^ n}
      mul_mem' := by
        rintro a b ⟨n, hn⟩ ⟨k, hk⟩
        exact ⟨n + k, by rw [map_mul, hn, hk, pow_add]⟩
      one_mem' := ⟨0, by rw [map_one, pow_zero]⟩
      inv_mem' := by
        rintro a ⟨n, hn⟩
        refine ⟨n * (D.nd.l i ^ m - 1), ?_⟩
        rw [map_inv, hn]
        symm
        apply eq_inv_of_mul_eq_one_left
        rw [← pow_add, show n * (D.nd.l i ^ m - 1) + n = D.nd.l i ^ m * n by
          rw [mul_comm n, ← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hL], pow_mul, hm, one_pow] }
  have hker : (D.ntw.psiL i).ker ≤ H := fun x hx => ⟨0, by rw [pow_zero]; exact hx⟩
  have hopen : IsOpen (H : Set (G D.host.E D.nd.Om)) := Subgroup.isOpen_mono hker (D.ntw.psiL_open i)
  have hclosed : IsClosed (H : Set (G D.host.E D.nd.Om)) := H.isClosed_of_isOpen hopen
  have hgen : Subgroup.closure (insert (D.nd.gam0 i v) {σ : G D.host.E D.nd.Om | ∀ y : D.nd.Om, y ≠ 0 →
      (D.nd.plOm.1 v).valuation (σ y / y - 1) < 1}) ≤ H := by
    rw [Subgroup.closure_le, Set.insert_subset_iff]
    refine ⟨⟨1, (pow_one _).symm⟩, fun σ hσ => ⟨0, ?_⟩⟩
    rw [pow_zero]
    exact hW D.host.E D.nd.Om (D.nd.l i) Fact.out v (D.nd.plOm.1 v) (D.nd.plOm.2 v) hl (D.nd.O i)ˣ
      (D.ntw.psiL i) (D.ntw.psiL_open i) (D.ntw.psiL_ord i) σ hσ
  have hT := (D.nd.restN_tameGenerator_generates i v (Or.inr hv)).2 hg
  exact closure_minimal hgen hclosed hT

end Formalism.MainNotions.N

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
section
noncomputable section

namespace Formalism.MainNotions.SphericalInertData

open Formalism.BasicNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual Polynomial Filter

section Iso

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

def IsBC (U : NBC A) (j : ℕ) (π : U.AU j) (Pa : List (Part A.CG)) : Prop :=
  (∀ p ∈ Pa, 1 ≤ p.a ∧ 1 ≤ p.d ∧ A.csd p.π) ∧
  (Pa.map fun p => ((⟨p.a, p.π⟩ : Σ a, A.CG a), p.d)).Nodup ∧
  rankIso N A Pa = R.nV ∧
  (∀ w, IsSplitPl H w → isoLoc N A Pa w = U.locAU j π w) ∧
  (∀ w, ¬ IsSplitPl H w → A.unr (isoLoc N A Pa w) ∧
    A.frobEig (isoLoc N A Pa w) = ubc R.nV (U.satAU j π w)) ∧
  ∀ τ, isoInf N A Pa τ = U.infW j (U.wtAU j π) τ

def SphInert (U : NBC A) (j : ℕ) (π : U.AU j) : Prop := ∀ w, ¬ IsSplitPl H w → U.sphAU j π w

end Iso

def HypCM (D : D7) : Prop :=
  (letI := D.host.cmStar; Formalism.HermitianLatticesTheory.IsCMUnram D.host.E) ∧
  2 ≤ Module.finrank ℚ D.host.F ∧
  ∀ w : PlE D.host, ¬ IsSplitPl D.host w → ((2 : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal

variable (D : D7)

def HypEFK : Prop :=
  Subfield.closure ((D.host.F : Set D.host.E) ∪ (D.host.K : Set D.host.E)) = ⊤

def BaseChangeSphericalInert : Prop :=
  HypCM D → ∀ j, 1 ≤ j → j ≤ D.R.m → 1 ≤ D.R.nV →
  (letI := D.host.cmStar; (D.sp.V j).IsDefinite) →
  ∀ π : D.nbc.AU j, SphInert D.nd D.naut D.nbc j π → ∃ Pa, IsBC D.nd D.naut D.nbc j π Pa

def BaseChangeGeneralInert : Prop :=
  HypCM D → ∀ j, 1 ≤ j → j ≤ D.R.m → 1 ≤ D.R.nV →
  (letI := D.host.cmStar; (D.sp.V j).IsDefinite) →
  ∀ PiC : D.naut.CG D.R.nV, D.naut.csd PiC → (∀ w, ¬ IsSplitPl D.host w → D.naut.unr (D.naut.locG PiC w)) →
    (∃ W : D.nbc.Wt j, ∀ τ, D.naut.infG PiC τ = D.nbc.infW j W τ) →
    ∃ π : D.nbc.AU j, (SphInert D.nd D.naut D.nbc j π ∧ IsBC D.nd D.naut D.nbc j π [⟨D.R.nV, PiC, 1⟩]) ∧ D.nbc.multAU j π = 1 ∧
      ∀ π' : D.nbc.AU j, SphInert D.nd D.naut D.nbc j π' ∧ IsBC D.nd D.naut D.nbc j π' [⟨D.R.nV, PiC, 1⟩] → π' = π

def Conclusion1 : Prop := HypEFK D → BaseChangeSphericalInert D

def Conclusion2 : Prop := HypEFK D → BaseChangeGeneralInert D

def aux₃ : Prop := Conclusion1 D ∧ Conclusion2 D

structure Pend : Prop where
  infG_card : ∀ {a} (π : D.naut.CG a) τ, Multiset.card (D.naut.infG π τ) = a
  ralg_iff : ∀ {a} (π : D.naut.CG a), D.naut.ralg π ↔
    ∀ τ, (D.naut.infG π τ).Nodup ∧ ∀ x ∈ D.naut.infG π τ, ∃ k : ℤ, x = (k : ℂ) + ((a : ℂ) - 1) / 2
  infG_tw : ∀ {a} (π : D.naut.CG a) (χ : D.naut.CG 1) τ (s : ℂ), D.naut.infG χ τ = {s} →
    D.naut.infG (D.naut.tw π χ) τ = (D.naut.infG π τ).map (· + s)
  csd_tw : ∀ {a} (π : D.naut.CG a) (χ : D.naut.CG 1), D.naut.csd χ → D.naut.csd π →
    D.naut.csd (D.naut.tw π χ)
  infW_alg : ∀ j (W : D.nbc.Wt j) τ, (D.nbc.infW j W τ).Nodup ∧
    ∀ x ∈ D.nbc.infW j W τ, ∃ k : ℤ, x = (k : ℂ) + ((D.R.nV : ℂ) - 1) / 2
  infW_inj : ∀ j (W W' : D.nbc.Wt j), D.nbc.infW j W = D.nbc.infW j W' → W = W'
  AU_ext : ∀ j (π π' : D.nbc.AU j),
    (∀ w, IsSplitPl D.host w → D.nbc.locAU j π w = D.nbc.locAU j π' w) →
    (∀ w, ¬ IsSplitPl D.host w → D.nbc.sphAU j π w ∧ D.nbc.sphAU j π' w ∧
      ubc D.R.nV (D.nbc.satAU j π w) = ubc D.R.nV (D.nbc.satAU j π' w)) →
    D.nbc.wtAU j π = D.nbc.wtAU j π' → π = π'

variable {D}

theorem isoLoc_single {a : ℕ} (P : D.naut.CG a) (w : PlE D.host) :
    isoLoc D.nd D.naut [⟨a, P, 1⟩] w = D.naut.locG P w := by
  have h0 : (((1 : ℕ) : ℝ) - 1) / 2 - ((0 : ℕ) : ℝ) = 0 := by norm_num
  show D.naut.lpSum (D.naut.lpSum (D.naut.lpTw (D.naut.locG P w) ((((1 : ℕ) : ℝ) - 1) / 2 - ((0 : ℕ) : ℝ)))
    (D.naut.lpZero w)) (D.naut.lpZero w) = D.naut.locG P w
  rw [D.naut.lpSum_zero, D.naut.lpSum_zero, h0, D.naut.lpTw_zero]

variable (D) in

def RalgHalf {a : ℕ} (π : D.naut.CG a) : Prop :=
  ∀ τ, (D.naut.infG π τ).Nodup ∧ ∀ x ∈ D.naut.infG π τ, ∃ k : ℤ, x = (k : ℂ) + (a : ℂ) / 2

theorem Pend.part_entries (hP : Pend D) {j : ℕ} {π : D.nbc.AU j} {Pa : List (Part D.naut.CG)}
    (h : IsBC D.nd D.naut D.nbc j π Pa) (p : Part D.naut.CG) (hp : p ∈ Pa) (τ : D.host.E →+* ℂ) :
    (D.naut.infG p.π τ).Nodup ∧ ∀ x ∈ D.naut.infG p.π τ, ∃ k : ℤ,
      x = (k : ℂ) + ((D.R.nV : ℂ) - p.d) / 2 := by
  obtain ⟨h1, -, -, -, -, h6⟩ := h
  have hd : 1 ≤ p.d := (h1 p hp).2.1
  have hsub : (D.naut.infG p.π τ).map (· + (((p.d : ℂ) - 1) / 2 - ((0 : ℕ) : ℂ))) ≤
      isoInf D.nd D.naut Pa τ := by
    unfold isoInf
    refine le_trans ?_ (List.le_sum_of_mem (List.mem_map.mpr ⟨p, hp, rfl⟩))
    apply List.le_sum_of_mem
    rw [List.mem_map]
    refine ⟨((0 : ℕ) : ℂ), ?_, rfl⟩
    simp
    exact ⟨0, hd, by simp⟩
  rw [h6 τ] at hsub
  obtain ⟨hnd, hent⟩ := hP.infW_alg j (D.nbc.wtAU j π) τ
  refine ⟨Multiset.Nodup.of_map _ (Multiset.nodup_of_le hsub hnd), fun x hx => ?_⟩
  obtain ⟨k, hk⟩ := hent _ (Multiset.mem_of_le hsub (Multiset.mem_map_of_mem _ hx))
  refine ⟨k, ?_⟩
  push_cast at hk ⊢
  linear_combination hk

theorem Pend.part_alg (hP : Pend D) {j : ℕ} {π : D.nbc.AU j} {Pa : List (Part D.naut.CG)}
    (h : IsBC D.nd D.naut D.nbc j π Pa) (p : Part D.naut.CG) (hp : p ∈ Pa) :
    D.naut.ralg p.π ∨ RalgHalf D p.π := by
  have he := fun τ => hP.part_entries h p hp τ
  rcases Int.even_or_odd ((D.R.nV : ℤ) - p.d - p.a + 1) with ⟨t, ht⟩ | ⟨t, ht⟩
  · left
    rw [hP.ralg_iff]
    intro τ
    refine ⟨(he τ).1, fun x hx => ?_⟩
    obtain ⟨k, hk⟩ := (he τ).2 x hx
    refine ⟨k + t, ?_⟩
    have ht' : ((D.R.nV : ℂ) - p.d - p.a + 1) = (t : ℂ) + t := by exact_mod_cast ht
    push_cast
    linear_combination hk + ht' / 2
  · right
    intro τ
    refine ⟨(he τ).1, fun x hx => ?_⟩
    obtain ⟨k, hk⟩ := (he τ).2 x hx
    refine ⟨k + t, ?_⟩
    have ht' : ((D.R.nV : ℂ) - p.d - p.a + 1) = 2 * (t : ℂ) + 1 := by exact_mod_cast ht
    push_cast
    linear_combination hk + ht' / 2

variable (D)

def adm5 : Prop :=
  ∀ (a : ℕ) (π : D.naut.CG a), 1 ≤ a → D.naut.csd π → D.naut.ralg π →
  ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ),
  ∃ r : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l), Continuous r ∧
    ∀ᶠ w in cofinite, ∀ (B : ValuationSubring D.nd.Om) (σ : G D.host.E D.nd.Om),
      IsPlaceOver (F := D.host.E) B w → IsFrob (F := D.host.E) B (normV w) σ →
      ((r σ : Matrix (Fin a) (Fin a) (Qbar l)).charpoly).map ι.toRingHom =
        galPol D.naut (D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2))

def GaloisRepHalfAlgebraic : Prop :=
  ∀ (a : ℕ) (π : D.naut.CG a), 1 ≤ a → D.naut.csd π → RalgHalf D π →
  ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ),
  ∃ r : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l), Continuous r ∧
    ∀ᶠ w in cofinite, ∀ (B : ValuationSubring D.nd.Om) (σ : G D.host.E D.nd.Om),
      IsPlaceOver (F := D.host.E) B w → IsFrob (F := D.host.E) B (normV w) σ →
      ((r σ : Matrix (Fin a) (Fin a) (Qbar l)).charpoly).map ι.toRingHom =
        galPol D.naut (D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2 + 1 / 2))

def MinkowskiCounting : Prop :=
  ∀ (a l : ℕ) [Fact l.Prime] (r r' : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)),
    Continuous r → Continuous r' →
    (∀ᶠ w in cofinite, IsSplitPl D.host w → ∀ (B : ValuationSubring D.nd.Om) (σ : G D.host.E D.nd.Om),
      IsPlaceOver (F := D.host.E) B w → IsFrob (F := D.host.E) B (normV w) σ →
      (r σ : Matrix (Fin a) (Fin a) (Qbar l)).charpoly = (r' σ : Matrix (Fin a) (Fin a) (Qbar l)).charpoly) →
    ∀ g, (r g : Matrix (Fin a) (Fin a) (Qbar l)).charpoly = (r' g : Matrix (Fin a) (Fin a) (Qbar l)).charpoly

def adm6 : Prop :=
  ∀ Pa Pa' : List (Part D.naut.CG),
    (∀ p ∈ Pa, 1 ≤ p.a ∧ 1 ≤ p.d ∧ D.naut.csd p.π) → (∀ p ∈ Pa', 1 ≤ p.a ∧ 1 ≤ p.d ∧ D.naut.csd p.π) →
    (∀ᶠ w in cofinite, isoLoc D.nd D.naut Pa w = isoLoc D.nd D.naut Pa' w) → Pa.Perm Pa'

def adm7 : Prop :=
  ∀ (L : Type) [Field L] (σ : L ≃+* L), σ ≠ RingEquiv.refl L → (∀ x, σ (σ x) = x) →
    ∀ x : L, x * σ x = 1 → ∃ y : L, y ≠ 0 ∧ x = y / σ y

def ConjugateSelfDualCharacter : Prop :=
  HypCM D → ∃ μ : D.naut.CG 1, D.naut.csd μ ∧
    (∀ w, ¬ IsSplitPl D.host w → D.naut.unr (D.naut.locG μ w) ∧
      D.naut.frobEig (D.naut.locG μ w) = {-1}) ∧
    ∀ τ, ∀ x ∈ D.naut.infG μ τ, ∃ k : ℤ, x = (k : ℂ) + 1 / 2

def admitted : Prop := adm5 D ∧ GaloisRepHalfAlgebraic D ∧ MinkowskiCounting D ∧ adm6 D ∧ ConjugateSelfDualCharacter D

def Stmt : Prop := Pend D → admitted D → aux₃ D

end Formalism.MainNotions.SphericalInertData

end
end

