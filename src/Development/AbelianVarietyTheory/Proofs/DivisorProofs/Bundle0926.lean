import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapRangeAdjointLeBlockSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0902
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0887
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0891
import Formalism.PairingDivisors.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Formalism.LocalToGlobal.ProjectiveLattices.HostInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0903
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0027
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0030
import Formalism.LocalToGlobal.CMDeterminantIdeals.Bundle0001
import Formalism.PolynomialDimension.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftsEquivariant
section
noncomputable section

open Polynomial Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links

namespace GlobalTheory.AdjBlock

section Record

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def HeckeNormal {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (J : Subgroup (GA D V)) (H : HMod (MMap M))
    {Pl0 : Type} (ok : Set Pl0) (pl : Pl0 → Pl D.host.E) : Prop :=
  ∃ T : ok × ℕ → Module.End ℂ H.H, (∀ P, T (P, 0) = 1) ∧
    (∀ (P : ok) (k : ℕ), k ≤ V.rank → ∀ α : GA D V, IsHeckeAt V (pl P) k α → ∀ B : Finset (GA D V),
      Bridge.IsDC J α⁻¹ B → ∀ x, H.e (T (P, k) x) = heckeOn M B (H.e x)) ∧
    Col.PairComm T ∧ ∀ i, Commute (T i) (LinearMap.adjoint (T i))

def IsDefEig (V : HSp D) (J : Subgroup (Bridge.Gf V)) {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    {Pl0 : Type} (ok : Set Pl0) (pl : Pl0 → Pl D.host.E) (q : Pl0 → ℕ) (g : ok → ℂ[X]) (f : Bridge.Gf V → W) : Prop :=
  ∀ i : ok × ℕ, 1 ≤ i.2 → i.2 ≤ V.rank → ∀ x : Bridge.Gf V, isTEnv V pl ok i x → ∀ B : Finset (Bridge.Gf V),
    (∀ a ∈ B, isLocEnv V pl ok i a) → Bridge.IsDC J x B → Bridge.dcOp B f = eigOf (q i.1) (g i.1) i.2 • f

open Classical in

def polOf {Pl0 : Type} (ok : Set Pl0) (r : ℕ) (q : Pl0 → ℕ) (c : ok × ℕ → ℂ) (P : Pl0) : ℂ[X] :=
  if h : P ∈ ok then Col.heckePoly r (fun P : ok => q P) c ⟨P, h⟩ else 1

theorem polOf_apply {Pl0 : Type} (ok : Set Pl0) (r : ℕ) (q : Pl0 → ℕ) (c : ok × ℕ → ℂ) (P : ok) :
    polOf ok r q c P = Col.heckePoly r (fun P : ok => q P) c P := dif_pos P.2

theorem mem_hPart {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {J : Subgroup (GA D V)} {H : HMod (MMap M)}
    {Pl0 : Type} {ok : Set Pl0} {pl : Pl0 → Pl D.host.E} {q : Pl0 → ℕ} (hq : ∀ P : ok, 0 < q P)
    {T : ok × ℕ → Module.End ℂ H.H}
    (hT : ∀ (P : ok) (k : ℕ), k ≤ V.rank → ∀ α : GA D V, IsHeckeAt V (pl P) k α → ∀ B : Finset (GA D V),
      Bridge.IsDC J α⁻¹ B → ∀ x, H.e (T (P, k) x) = heckeOn M B (H.e x))
    {c : ok × ℕ → ℂ} {e : H.H} (he : ∀ i, T i e = c i • e) :
    H.e e ∈ hPart M J ok pl q (polOf ok V.rank q c) := by
  simp only [hPart, Submodule.mem_iInf, LinearMap.mem_ker]
  intro P hP k hk α hα B hB
  have h1 := eigOf_heckePolyOf (hq ⟨P, hP⟩) (fun k => c (⟨P, hP⟩, k)) hk
  have h2 : polOf ok V.rank q c P = _ := polOf_apply ok V.rank q c ⟨P, hP⟩
  rw [LinearMap.sub_apply, ← hT ⟨P, hP⟩ k hk α hα B hB, he, map_smul, LinearMap.smul_apply, LinearMap.id_apply, h2,
    sub_eq_zero]
  exact congrArg (· • H.e e) h1.symm

theorem side_le {G Pl0 : Type} [Group G] [Fintype G] {V Y : HSp D} {c : CoefA V} {β : GL (Fin V.rank) (EAf D)}
    {L : LevDat D.host.E ℂ V.rank} {pl : Pl0 → Pl D.host.E} {ok : Set Pl0} {S : CSD D.what₂.LL}
    {act : Representation D.what₂.LL G S.Forms} {op : ok × ℕ → Module.End D.what₂.LL S.Forms}
    (B : Bridge.SideReal D V (Bridge.envOf c.coef (levEnvOf V β L pl ok)) S act op fun i => i.2)
    (N : HMod (Bridge.Gf V → c.W))
    (hN : N.Is (Bridge.AdForms (Bridge.ratF V) c.coef.ρ (levEnv V β L).J (levEnv V β L).χ)
      (Bridge.adInner (Bridge.ratF V) (levEnv V β L).J B.pres.y))
    {j : S.Forms →ₛₗ[D.what₂.embLL] N.H} (hj : ∀ x, N.e (j x) = B.pres.extL x)
    (hc : Col.PairComm op) (hs : Col.SplitOver op) {q : Pl0 → ℕ} (hq : ∀ P : ok, 0 < q P) {t n : ℕ}
    {bl : List (ok → D.what₂.LL)} (hV : V.rank = n) (hn : n = Y.rank + bl.length * t)
    (hdeg : ∀ P, op (P, 0) = 1 ∧ ∀ k, V.rank < k → op (P, k) = 0)
    {SY : D.what₂.Tau → SPar} {M : DSModel Y SY} {J : Subgroup (GA D Y)} {H : HMod (MMap M)}
    (hT : HeckeNormal M J H ok pl) (Θ : N.H →ₗ[ℂ] H.H) (s : ok → ℂ)
    (hup : ∀ f : Pl0 → ℂ[X], (∀ P ∈ ok, (f P).natDegree ≤ Y.rank) → ∀ e : H.H, H.e e ∈ hPart M J ok pl q f →
      IsDefEig V (levEnv V β L).J ok pl q (fun P => (f P).comp (C (s P) * X) *
        ((bl.map fun ν => Col.blockPoly (ν P) (q P) t).prod).map D.what₂.embLL) (N.e (LinearMap.adjoint Θ e))) :
    (LinearMap.range (LinearMap.adjoint Θ)).comap j ≤ Col.blockSum n (fun P : ok => q P) t bl op := by
  subst hV
  have hf := model_form (W := c.W) (ι := Bridge.ratF V) (ρ := c.coef.ρ) (J := (levEnv V β L).J) (χ := (levEnv V β L).χ)
    B.pres N hN hj
  obtain ⟨T, hT0, hTt, hTc, hTn⟩ := hT
  refine comap_range_adjoint_le_blockSum (r := Y.rank) (q := fun P : ok => q P) hf.1 hf.2.1 hc hs hq hn
    (fun P => (hdeg P).1) (fun P => (hdeg P).2) Θ hT0 hTc hTn s ?_
  intro x e he P k hk1 hk U hU
  have h0 : ∀ P ∈ ok, (polOf ok Y.rank q x P).natDegree ≤ Y.rank := fun P hP => by
    have h : polOf ok Y.rank q x P = _ := polOf_apply ok Y.rank q x ⟨P, hP⟩
    rw [h]
    exact natDegree_heckePolyOf _ _ _
  have h3 := hup (polOf ok Y.rank q x) h0 e (mem_hPart hq hTt he) (P, k) hk1 hk _ (B.hecke.hx_ok (P, k) ⟨hk1, hk⟩) _
    (B.hecke.hA_loc (P, k) ⟨hk1, hk⟩) (B.hecke.hDC (P, k) ⟨hk1, hk⟩)
  have h4 := (model_dcOp (W := c.W) (ι := Bridge.ratF V) (ρ := c.coef.ρ) (J := (levEnv V β L).J) (χ := (levEnv V β L).χ)
    B.pres N hN hj (B.hecke.op_eq (P, k) ⟨hk1, hk⟩) hU _).trans h3
  simp only [polOf_apply] at h4
  have hinj : Function.Injective N.e := hN.1
  exact hinj (h4.trans (N.e.map_smul _ _).symm)

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

def HeckeOps : Prop :=
  (∀ t, HeckeNormal (R.MY 0) (levG _ (R.βY 0) (R.dat0 R.triv)) R.HE (A.ok t) R.pl) ∧
    ∀ i t, HeckeNormal (R.MW i (sg0 D A)) (levG _ (R.βW i) (R.datWp i R.triv)) (R.HW i (sg0 D A)) (A.ok t) R.pl

def HeckeUpRows : Prop :=
  ∀ (t : T) (f : Pl0 → ℂ[X]), (∀ P ∈ A.ok t, (f P).natDegree ≤ (Yc D 0).rank) → ∀ e : R.HE.H,
    R.HE.e e ∈ hPart (R.MY 0) (levG _ (R.βY 0) (R.dat0 R.triv)) (A.ok t) R.pl A.q f →
      IsDefEig D.sp.X' (levEnv _ R.βX (R.datXt t)).J (A.ok t) R.pl A.q
        (fun P => (f P).comp (C ((A.q P : ℂ) ^ (D.R.m / 2 * D.R.t)) * X) * ((A.fam.R t).blockProd P).map D.what₂.embLL)
        ((R.HX t).e (LinearMap.adjoint (R.Th t) e))

def HeckeUpLifts : Prop :=
  ∀ (i : Fin D.R.m) (t : T) (f : Pl0 → ℂ[X]), (∀ P ∈ A.ok t, (f P).natDegree ≤ (Wc D i).rank) →
    ∀ w : (R.HW i (sg0 D A)).H,
    (R.HW i (sg0 D A)).e w ∈ hPart (R.MW i (sg0 D A)) (levG _ (R.βW i) (R.datWp i R.triv)) (A.ok t) R.pl A.q f →
      IsDefEig (Vc D i) (levEnv _ (R.βV i) (R.datVt i t)).J (A.ok t) R.pl A.q
        (fun P => (f P).comp (C (D.what₂.embLL (A.etaVal P : D.what₂.LL) * (A.q P : ℂ) ^ ((D.R.t + 1) / 2)) * X) *
          ((A.fam.L i t).blockProd P).map D.what₂.embLL)
        ((R.HV i t).e (LinearMap.adjoint (R.thG i t) w))

def LiftsEquivariant : Prop :=
  (∀ t g (v : (A.MtildeCSD t).Forms), R.Th t (R.jX t (A.leftGroupActionRight t g v)) = R.gE g (R.Th t (R.jX t v))) ∧
    ∀ i t g (v : (A.MtCSD i t).Forms),
      R.thG i t (R.jV i t (A.leftGroupActionLift i t g v)) = R.gW i (sg0 D A) g (R.thG i t (R.jV i t v))

theorem postOn_gaL {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (β : GL (Fin V.rank) (EAf D))
    (L : LevDat D.host.E ℂ V.rank) (eG : G ≃* G0 L.Pg L.r) (c : G → ℂ) (x : MMap M) :
    postOn M (gaL V β L eG c) x = ∑ g, c g • postOn M (actL V β L (eG g)) x := by
  ext v h
  simp [postOn, gaL, LinearMap.sum_apply, Finset.sum_apply]

variable {R} {F : Face D A}

theorem proj_rows (hC : R.Char F) (y : R.HE.H) : ∑ g, D.what₂.embLL ((idemOf A.X).coeff g) • R.gE g y = y := by
  refine hC.models.HE.1 ?_
  have h1 : R.HE.e y ∈ R.EEat R.triv := by
    rw [← hC.models.HE.2.1]
    exact LinearMap.mem_range_self _ y
  have h2 : postOn (R.MY 0) R.e0 (R.HE.e y) - R.HE.e y = 0 := h1.2
  refine Eq.trans ?_ ((postOn_gaL (R.MY 0) (R.βY 0) (R.dat0 R.triv) R.eG _ _).symm.trans (sub_eq_zero.1 h2))
  rw [map_sum]
  exact Finset.sum_congr rfl fun g _ => by rw [map_smul, hC.models.gE]; rfl

theorem proj_lifts {s : ℕ} (hC : R.Char F) (hOk : A.fam.Ok s) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) :
    ∑ g, D.what₂.embLL ((idemOf A.X).coeff g) • R.gW i (sg0 D A) g (R.thG i t y) = R.thG i t y := by
  have h1 : R.thF i t y ∈ LinearMap.range (R.HW i (sg0 D A)).e :=
    (hC.models.HW i (sg0 D A)).2.1.ge (hC.thP.thF_mem i t y)
  obtain ⟨z, hz⟩ := h1
  have hs : ∀ a, sg0 D A a = D.what₂.embLL a := fun a => by rw [sg0, sgAt_mk _ R.hv0]
  have h2 : R.thG i t y = ∑ g, D.what₂.embLL ((idemOf A.X).coeff g) • R.gW i (sg0 D A) g z := by
    refine (hC.models.HW i _).1 ?_
    rw [hC.thP.thG, ← hz, map_sum]
    refine (postOn_gaL (R.MW i (sg0 D A)) (R.βW i) (R.datWp i R.triv) R.eG _ _).trans ?_
    exact Finset.sum_congr rfl fun g _ => by rw [map_smul, hC.models.gW, RealDat.eC, hs]; rfl
  rw [h2]
  exact idem_idem _ hOk.irr _ z

theorem r_eq (hC : R.Char F) : A.r = D.R.r := hC.fam.tie.choose_spec.choose_spec.choose_spec.ranks.2.1

theorem rows_le {s : ℕ} (hC : R.Char F) (hOk : A.fam.Ok s) (hT : HeckeOps R) (hR : HeckeUpRows R)
    (hG : LiftsEquivariant R) (t : T) :
    (LinearMap.range (LinearMap.adjoint (R.Th t))).comap (R.jX t) ≤ (A.fam.R t).ZHg A.X := by
  have hrk : (Yc D 0).rank = A.r := by
    rw [D.sp.Y_rank _ (min_le_right _ _), r_eq hC]
    simp [Ranks.rankY]
  have hn : (A.fam.R t).n = (Yc D 0).rank + (A.fam.R t).bl.length * (A.fam.R t).t := by
    rw [hrk]
    exact congrArg (fun k => A.r + k * A.t) List.length_ofFn.symm
  exact le_inf
    (side_le (R.B.R t) (R.HX t) (hC.models.HX t) (hC.models.jX t) (hOk.what₂ t).comm (hOk.what₂ t).split (q := A.q)
      (hOk.what₂ t).q_pos R.B.rankR hn (hC.fam.degR t) (hT.1 t) (R.Th t) _ (hR t))
    (model_good (W := R.cX.W) (ι := Bridge.ratF D.sp.X') (ρ := R.cX.coef.ρ) (J := (levEnv _ R.βX (R.datXt t)).J)
      (χ := (levEnv _ R.βX (R.datXt t)).χ) (R.B.R t).pres (R.HX t) (hC.models.HX t) (hC.models.jX t) (hOk.what₂ t).act hOk.irr R.gE (hG.1 t)
      fun y => proj_rows hC _)

theorem lifts_le {s : ℕ} (hC : R.Char F) (hOk : A.fam.Ok s) (hT : HeckeOps R) (hL : HeckeUpLifts R)
    (hG : LiftsEquivariant R) (i : Fin D.R.m) (t : T) :
    (LinearMap.range (LinearMap.adjoint (R.thG i t))).comap (R.jV i t) ≤ (A.fam.L i t).ZHg A.X := by
  have hrk : (Wc D i).rank = A.r := by
    rw [D.sp.W_rank _ (Nat.le_add_left _ _) i.2, r_eq hC]
  have hn : (A.fam.L i t).n = (Wc D i).rank + (A.fam.L i t).bl.length * (A.fam.L i t).t := by
    rw [hrk]
    show A.r + A.t = A.r + 1 * A.t
    rw [one_mul]
  exact le_inf
    (side_le (R.B.L i t) (R.HV i t) (hC.models.HV i t) (hC.models.jV i t) (hOk.lifts i t).comm (hOk.lifts i t).split
      (q := A.q) (hOk.lifts i t).q_pos (R.B.rankL i) hn (hC.fam.degL i t) (hT.2 i t) (R.thG i t) _ (hL i t))
    (model_good (W := (R.cV i).W) (ι := Bridge.ratF (Vc D i)) (ρ := (R.cV i).coef.ρ)
      (J := (levEnv _ (R.βV i) (R.datVt i t)).J) (χ := (levEnv _ (R.βV i) (R.datVt i t)).χ) (R.B.L i t).pres (R.HV i t) (hC.models.HV i t) (hC.models.jV i t) (hOk.lifts i t).act hOk.irr
      (R.gW i (sg0 D A)) (hG.2 i t) fun y => proj_lifts hC hOk i t y)

theorem lBlock {s : ℕ} (hC : R.Char F) (hOk : A.fam.Ok s) (hT : HeckeOps R) (hR : HeckeUpRows R) (hL : HeckeUpLifts R)
    (hG : LiftsEquivariant R) : R.LBlock F :=
  ⟨fun t x hx => rows_le hC hOk hT hR hG t ((mem_range_adjoint_tw (twAt D.what₂.embLL A.v0) (R.Th t) (R.jX t x)).1 hx),
    fun i t x hx => lifts_le hC hOk hT hL hG i t
      ((mem_range_adjoint_tw (twAt D.what₂.embLL A.v0) (R.thG i t) (R.jV i t x)).1 hx)⟩

end Record

end GlobalTheory.AdjBlock

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAdelicSchwartzSpaceOfLevelCompactSchwartzStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_adelicSchwartzSpace_of_level_compact_schwartz : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) (Φ : (Fin N → AF F) → ℂ), (∃ U : AddSubgroup (Fin N → AF F), IsOpen (U : Set (Fin N → AF F)) ∧ ∀ u ∈ U, inf u = 0 → ∀ x, Φ (x + u) = Φ x) → (∃ K : Set (Fin N → Af F), IsCompact K ∧ ∀ x, Φ x ≠ 0 → fin x ∈ K) → (∀ x, ∃ g : SchwartzMap (Fin N → mixedEmbedding.mixedSpace F) ℂ, ∀ t, g t = Φ (x + embR t)) → Φ ∈ GlobalTheory.WeilM.schA F (Fin N) := by
  first | exact @GlobalTheory.LevelSchwartz.mem_schA_of_level | exact GlobalTheory.LevelSchwartz.mem_schA_of_level | (intros; apply GlobalTheory.LevelSchwartz.mem_schA_of_level <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemClosureSpecialUnitarySupportedAtPlaces
section
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct
open Filter Topology

namespace GlobalTheory.SUTrunc

section Mat

variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] {e : R}

theorem idempotentTruncation_preserves_form (he : e * e = e) {A B J : Matrix n n R} (h : A * J * B = J) :
    (1 + e • (A - 1)) * J * (1 + e • (B - 1)) = J := by
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.one_mul, Matrix.mul_one, smul_add, smul_sub, smul_smul, he, h]
  abel

theorem trunc_mul (he : e * e = e) {A B : Matrix n n R} (h : A * B = 1) :
    (1 + e • (A - 1)) * (1 + e • (B - 1)) = 1 := by
  have := idempotentTruncation_preserves_form he (A := A) (B := B) (J := 1) (by rw [Matrix.mul_one, h])
  rwa [Matrix.mul_one] at this

theorem cT_trunc (c : R →+* R) (hc : c e = e) (A : Matrix n n R) :
    Formalism.UG.cT c (1 + e • (A - 1)) = 1 + e • (Formalism.UG.cT c A - 1) := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [Formalism.UG.cT, hc]
  · simp [Formalism.UG.cT, hc, Matrix.one_apply_ne h, Matrix.one_apply_ne (Ne.symm h)]

theorem det_trunc (he : e * e = e) {A : Matrix n n R} (h : A.det = 1) : (1 + e • (A - 1)).det = 1 := by
  have key : ∀ (a : R) (B : Matrix n n R), B.det = 1 → (∀ i j, a ∣ (1 + e • (A - 1)) i j - B i j) →
      a ∣ (1 + e • (A - 1)).det - 1 := by
    intro a B hB hd
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq, RingHom.map_det, ← hB, RingHom.map_det]
    congr 1
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
    exact hd i j
  obtain ⟨x, hx⟩ := key e 1 Matrix.det_one fun i j => ⟨(A - 1) i j, by
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]; ring⟩
  obtain ⟨y, hy⟩ := key (1 - e) A h fun i j => ⟨-((A - 1) i j), by
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply]; ring⟩
  linear_combination (1 - e) * hx + e * hy + (-x - y) * he

end Mat

variable {F : Type} [Field F] [NumberField F]

theorem idem_mul_self {S₁ : Finset (InfinitePlace F)} {S₂ : Finset (HeightOneSpectrum (𝓞 F))} {η : AF F}
    (h : IsPlacesIdem S₁ S₂ η) : η * η = η := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine Prod.ext (funext fun w => ?_) (RestrictedProduct.ext _ _ fun v => ?_)
  · change fstA F η w * fstA F η w = fstA F η w
    by_cases hw : w ∈ S₁
    · rw [h1 w hw, mul_one]
    · rw [h2 w hw, mul_zero]
  · change evalV F v (sndA F η) * evalV F v (sndA F η) = evalV F v (sndA F η)
    by_cases hw : v ∈ S₂
    · rw [h3 v hw, mul_one]
    · rw [h4 v hw, mul_zero]

theorem tendsto_idem (η : Finset (HeightOneSpectrum (𝓞 F)) → AF F)
    (hη : ∀ T, IsPlacesIdem Finset.univ T (η T)) : Tendsto η atTop (𝓝 1) := by
  classical
  let y : Finset (HeightOneSpectrum (𝓞 F)) → ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F :=
    fun T v => if v ∈ T then 1 else 0
  have hy : Tendsto y atTop (𝓝 1) := by
    rw [tendsto_pi_nhds]
    intro v
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop {v}] with T hT
    exact (if_pos (hT (Finset.mem_singleton_self v))).symm
  let s : (∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) → Af F :=
    RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) cofinite
  have hs : Continuous s := RestrictedProduct.isEmbedding_structureMap.continuous
  have hp : Continuous fun z => pairA F 1 (s z) := continuous_const.prodMk hs
  have h1 : pairA F 1 (s 1) = 1 := rfl
  have h2 : η = fun T => pairA F 1 (s (y T)) := by
    funext T
    obtain ⟨h1, -, h3, h4⟩ := hη T
    refine Prod.ext (funext fun w => h1 w (Finset.mem_univ w)) (RestrictedProduct.ext _ _ fun v => ?_)
    change evalV F v (sndA F (η T)) = ((y T v : v.adicCompletionIntegers F) : v.adicCompletion F)
    by_cases hv : v ∈ T
    · rw [h3 v hv]; simp [y, hv]
    · rw [h4 v hv]; simp [y, hv]
  rw [h2, ← h1]
  exact (hp.tendsto 1).comp hy

theorem mem_closure_supp : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ g ∈ SUAdelic σ J, g ∈ closure {x : HA (AF F) σ J | ∃ (T₁ : Finset (InfinitePlace F)) (T₂ : Finset (HeightOneSpectrum (𝓞 F))) (η : AF F), IsPlacesIdem T₁ T₂ η ∧ x ∈ SUSupp σ J η} := by
  intro F E _ _ _ _ _ σ _ M J _ g hg
  choose η hη using fun T : Finset (HeightOneSpectrum (𝓞 F)) => StrongApprox.exists_isPlacesIdem Finset.univ T
  have hlim := tendsto_idem η hη
  set ι := algebraMap (AF F) (AF F ⊗[F] E) with hι
  have he : ∀ T, ι (η T) * ι (η T) = ι (η T) := fun T => by rw [← map_mul, idem_mul_self (hη T)]
  let u : Finset (HeightOneSpectrum (𝓞 F)) → GL (Fin M) (AF F ⊗[F] E) := fun T =>
    ⟨1 + ι (η T) • (SUSuppSub.mv σ J g - 1), 1 + ι (η T) • (SUSuppSub.mv σ J g⁻¹ - 1),
      trunc_mul (he T) (SUSuppSub.mv_mul_inv σ J g), trunc_mul (he T) (SUSuppSub.mv_inv_mul σ J g)⟩
  have hu : ∀ T, u T ∈ HR (AF F) σ J := by
    intro T
    change Formalism.UG.cT (sigR (AF F) σ) (1 + ι (η T) • (SUSuppSub.mv σ J g - 1)) * JR (AF F) J *
      (1 + ι (η T) • (SUSuppSub.mv σ J g - 1)) = JR (AF F) J
    rw [cT_trunc _ (StrongApprox.sigR_algebraMap σ _)]
    exact idempotentTruncation_preserves_form (he T) (g : HR (AF F) σ J).2
  let x : Finset (HeightOneSpectrum (𝓞 F)) → HA (AF F) σ J := fun T => (⟨u T, hu T⟩ : HR (AF F) σ J)
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (AF F ⊗[F] E) := IsModuleTopology.toContinuousAdd (AF F) _
  have hmat : ∀ A : Matrix (Fin M) (Fin M) (AF F ⊗[F] E),
      Tendsto (fun T => 1 + ι (η T) • (A - 1)) atTop (𝓝 A) := by
    intro A
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
    have h := (hlim.smul_const ((A - 1) i j)).const_add ((1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j)
    rw [one_smul, Matrix.sub_apply, add_sub_cancel] at h
    refine h.congr fun T => ?_
    rw [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, Algebra.smul_def]
  have hx : Tendsto x atTop (𝓝 g) := by
    refine (tendsto_subtype_rng (p := fun a => a ∈ HR (AF F) σ J)).2 ?_
    rw [Units.isInducing_embedProduct.tendsto_nhds_iff]
    exact (hmat (SUSuppSub.mv σ J g)).prodMk_nhds
      ((MulOpposite.continuous_op.tendsto _).comp (hmat (SUSuppSub.mv σ J g⁻¹)))
  refine mem_closure_of_tendsto hx (Eventually.of_forall fun T => ⟨Finset.univ, T, η T, hη T, ?_⟩)
  rw [SUSuppSub.mem_SUSupp_iff]
  refine ⟨StrongApprox.mem_SUAdelic.2 (det_trunc (he T) (StrongApprox.mem_SUAdelic.1 hg)), ?_⟩
  change ι (η T) • (1 + ι (η T) • (SUSuppSub.mv σ J g - 1) - 1) = 1 + ι (η T) • (SUSuppSub.mv σ J g - 1) - 1
  rw [add_sub_cancel_left, smul_smul, he]

end GlobalTheory.SUTrunc

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCompletedOrderIffPlacewiseStatement
section
open NumberField IsDedekindDomain GlobalTheory.CMVal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_completedOrder_iff_placewise : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ z : Af E, z ∈ hatO c ↔ ∃ a ∈ hatF (E := E), (∀ w, Valued.v (a w) ≤ 1) ∧ ∀ (w : HeightOneSpectrum (𝓞 E)), Valued.v (z w - a w) ≤ WithZero.exp (-(multiplicity w.asIdeal (Ideal.map (algebraMap (OF E) (𝓞 E)) c) : ℤ)) := by
  first | exact @GlobalTheory.CMVal.HatPlace.mem_hatO_iff | exact GlobalTheory.CMVal.HatPlace.mem_hatO_iff | (intros; apply GlobalTheory.CMVal.HatPlace.mem_hatO_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMulInvIff
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links GlobalTheory.ChiGrid
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct nonZeroDivisors Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChiGrid.StairConj

theorem mem_mul_inv_iff {E : Type} [Field E] [NumberField E] (c : E → E) (hc : ∀ x, c (c x) = x)
    (hm : ∀ x y, c (x * y) = c x * c y) {A A' B B' : FractionalIdeal (𝓞 E)⁰ E} (hB : B ≠ 0) (hB' : B' ≠ 0)
    (hA : ∀ x, x ∈ A' ↔ c x ∈ A) (hBB : ∀ x, x ∈ B' ↔ c x ∈ B) (x : E) :
    x ∈ A' * B'⁻¹ ↔ c x ∈ A * B⁻¹ := by
  rw [← div_eq_mul_inv, ← div_eq_mul_inv, FractionalIdeal.mem_div_iff_of_ne_zero hB,
    FractionalIdeal.mem_div_iff_of_ne_zero hB']
  constructor
  · intro h y hy
    have h1 := (hA _).1 (h (c y) ((hBB _).2 (by rwa [hc])))
    rwa [hm, hc] at h1
  · intro h y hy
    rw [hA, hm]
    exact h _ ((hBB _).1 hy)

theorem mem_coe_iff (D : D7) (I : Ideal (𝓞 D.host.E)) (x : D.host.E) :
    x ∈ (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ↔
      D.host.conj x ∈ ((D.host.conj • I : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
  rw [FractionalIdeal.mem_coeIdeal, FractionalIdeal.mem_coeIdeal]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨D.host.conj • z, Ideal.smul_mem_pointwise_smul _ _ _ hz, rfl⟩
  · rintro ⟨z, hz, h⟩
    refine ⟨D.host.conj⁻¹ • z, Ideal.mem_pointwise_smul_iff_inv_smul_mem.1 hz, ?_⟩
    rw [Formalism.L2.Pj.algebraMap_gal_smul, Formalism.L2.Pj.conj_inv_apply, h, Formalism.L2.Pj.conj_conj]

theorem AA_ne_zero (D : D7) : D.host.AA ≠ 0 := by
  refine mul_ne_zero ?_ (inv_ne_zero (Formalism.L2.Pj.bB_ne D).1)
  rw [Ne, FractionalIdeal.coeIdeal_eq_zero]
  intro h
  exact D.host.ccK_ne_bot ((Ideal.map_eq_bot_iff_of_injective (RingOfIntegers.algebraMap.injective _ _)).1 h)

theorem conj_AA_and_stA : ∀ (D : D7), (D.host.AA ≠ 0 ∧ ∀ x, x ∈ D.host.AAbar ↔ star x ∈ D.host.AA) ∧ ∀ (T : Type) (L : LevCh D T) (P : Places L) (sc : Consts), P.stA sc ≠ 0 ∧ ∀ x, x ∈ P.stAbar sc ↔ star x ∈ P.stA sc := by
  intro D
  have hs : ∀ x : D.host.E, star x = D.host.conj x := bridge_star_holds D.R D.host
  have hA : ∀ x, x ∈ D.host.AAbar ↔ D.host.conj x ∈ D.host.AA := fun x =>
    ⟨Formalism.L2.Pj.conj_mem_AA D, fun ha => by
      simpa only [Formalism.L2.Pj.conj_conj] using Formalism.L2.Pj.conj_mem_AAbar D ha⟩
  refine ⟨⟨AA_ne_zero D, fun x => by rw [hs]; exact hA x⟩, fun T L P sc => ?_⟩
  have h1 : ((P.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]; exact P.modul_ne_bot sc
  have h2 : ((P.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := by
    intro h
    apply h1
    rw [FractionalIdeal.eq_zero_iff] at h ⊢
    intro x hx
    have := h _ ((mem_coe_iff D _ x).1 hx)
    exact (map_eq_zero _).1 this
  refine ⟨mul_ne_zero (AA_ne_zero D) (inv_ne_zero h2), fun x => ?_⟩
  rw [hs]
  exact mem_mul_inv_iff D.host.conj (Formalism.L2.Pj.conj_conj D) (map_mul _) h2 h1 hA (mem_coe_iff D _) x

end GlobalTheory.ChiGrid.StairConj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MetricScalarPoincareWeightEqTwoMulPotential
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst GlobalTheory.ScalarPoin MeasureTheory

namespace GlobalTheory.ScalarPoin

theorem phla_laS_cpt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r)
    (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ (k : ℕ) (z : ReciprocityTheory.L2DbarEstimates.V (nd X)), z ∈ OmF X x0 →
    phla X (laS X k) (cpt X x0 z) = 2 * (k : ℝ) * rhF X x0 z := by
  intro E _ _ _ r X x0 ho k z hz
  rw [IW.phla_eq X hz, rhF, ← Finset.sum_neg_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  set x := cpt X x0 z
  let L' : ℕ → ℝ := fun j => if h : j < r + 1 then IW.Lm X x τ ⟨j, h⟩ else 0
  have h1 : ∀ i : Fin r, IW.Lm X x τ i.succ = L' (i + 1) := fun i => by
    simp only [L', dif_pos (Nat.succ_lt_succ i.isLt)]; rfl
  have h2 : ∀ i : Fin r, IW.Lm X x τ i.castSucc = L' i := fun i => by
    simp only [L', dif_pos (Nat.lt_succ_of_lt i.isLt)]; rfl
  have hk : ∀ i : Fin r, ((laS X k τ i : ℤ) : ℝ) =
      2 * (k : ℝ) * (if (i : ℕ) < X.p0 then (0 : ℝ) else 1) - (k : ℝ) := fun i => by
    unfold laS
    by_cases h : (i : ℕ) < X.p0
    · rw [if_neg (not_le.2 h), if_pos h]; push_cast; ring
    · rw [if_pos (not_lt.1 h), if_neg h]; push_cast; ring
  have hL0 : L' 0 = 0 := by
    simp only [L', dif_pos (Nat.succ_pos r)]; exact IW.Lm_zero X x τ
  have hLr : L' r = 0 := by
    simp only [L', dif_pos (Nat.lt_succ_self r)]; exact IW.Lm_last_cpt X x0 ho z τ
  have hLp : L' X.p0 = Real.log ‖dmin X.Gm x τ ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩‖ := by
    simp only [L', dif_pos (Nat.lt_succ_of_le X.p0_le)]; rfl
  simp_rw [h1, h2, hk]
  rw [Fin.sum_univ_eq_sum_range
    (fun i => (2 * (k : ℝ) * (if i < X.p0 then (0 : ℝ) else 1) - (k : ℝ)) * (L' (i + 1) - L' i)) r]
  have hsplit : ∑ i ∈ Finset.range r,
      (2 * (k : ℝ) * (if i < X.p0 then (0 : ℝ) else 1) - (k : ℝ)) * (L' (i + 1) - L' i) =
      2 * (k : ℝ) * ∑ i ∈ Finset.range r, (if i < X.p0 then (0 : ℝ) else 1) * (L' (i + 1) - L' i) -
        (k : ℝ) * ∑ i ∈ Finset.range r, (L' (i + 1) - L' i) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hsplit, GlobalTheory.CurvMargin.tele_tail L' X.p0 r X.p0_le, Finset.sum_range_sub L' r, hLr, hL0, hLp]
  ring

end GlobalTheory.ScalarPoin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulNormDualWeylTensorEvaluationLeFibreNormStatement
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mul_norm_dualWeylTensorEvaluation_le_fibreNorm : ∀ (T : Type) [Fintype T] [DecidableEq T] (N : T → ℕ) (la : ∀ t, Fin (N t) → ℕ), (∀ t, Antitone (la t)) → ∀ (x : TIdx la → ℂ) (X : ∀ t, Matrix (Fin (N t)) (Fin (N t)) ℂ) (u : ∀ t, UN (N t)) (s : ℝ), 0 ≤ s → s * ‖tval la x (fun t => X t * (u t).1)‖ ≤ Real.sqrt (∑ I, ‖(fibY la s X *ᵥ x) I‖ ^ 2) := by
  first | exact @GlobalTheory.TSup.mul_norm_tval_le_fibNorm | exact GlobalTheory.TSup.mul_norm_tval_le_fibNorm | (intros; apply GlobalTheory.TSup.mul_norm_tval_le_fibNorm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormGaloisConjHeckeCharacterFinitePartEqOneStatement
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open GlobalTheory.ToricTransport (coordIn)
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_galois_conj_heckeCharacter_finitePart_eq_one : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {I : Type} [Fintype I] (φ : I → E →+* ℂ) (hφ : IsCMType φ) (s : ℕ) (κ : I → ℕ) (c : Ideal (OF E)) (hc : c ≠ ⊥) (χ : HChar E) (hχ : HasInf χ φ (fun i => (κ i : ℤ) + s)) (hu : ∀ u ∈ hatOUnits c, finPart χ u = 1) (σ : ℂ ≃+* ℂ) (y : (Af E)ˣ), ‖σ (finPart χ y : ℂ)‖ = 1 := by
  first | exact @GlobalTheory.CMVal.norm_conj_finPart | exact GlobalTheory.CMVal.norm_conj_finPart | (intros; apply GlobalTheory.CMVal.norm_conj_finPart <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormOneQuaternionNearConjRationalTimesSupportedStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normOneQuaternion_near_conj_rational_times_supported : ∀ (F : Type) [Field F] [NumberField F] (a b : F), a ≠ 0 → b ≠ 0 → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (S₁.Nonempty ∨ S₂.Nonempty) → (∀ t : AF F, ∃ h : DA F a b, nrm h = 1 ∧ ε * h.re = ε * t) → ∀ g : DA F a b, nrm g = 1 → ε • (g - 1) = 0 → ∀ W : Set (DA F a b), W ∈ 𝓝 g → ∃ w ∈ W, ∃ y : DA F a b, IsUnit (nrm y) ∧ ∃ γ : ℍ[F, a, b], nrm γ = 1 ∧ ∃ h : DA F a b, nrm h = 1 ∧ ε • (h - 1) = h - 1 ∧ y * w = rat γ * y * h := by
  first | exact @GlobalTheory.QSAStep.key_step | exact GlobalTheory.QSAStep.key_step | (intros; apply GlobalTheory.QSAStep.key_step <;> assumption)
end

