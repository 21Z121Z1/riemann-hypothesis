import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0025
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0028
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0017
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0012
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0026
import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProofFree
import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProof

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.ChiProofs
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Models

variable {D : D7} {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}

theorem adel_leftInv_of_inv {X : Comp → Data E r} (V : HSp D) (dict : GA D V → Σ k, Frame (X k).Ψ r)
    (mu : GA D V → ℂ) (P : FDSec X)
    (hd : ∀ γ ∈ GQ V, ∀ g, ∃ γ' ∈ (X (dict g).1).Γ, dict (γ * g) = ⟨(dict g).1, lact γ' (dict g).2⟩)
    (hm : MuUnit V dict mu)
    (hP : ∀ g, ∀ γ' ∈ (X (dict g).1).Γ, P (dict g).1 (lact γ' (dict g).2) = P (dict g).1 (dict g).2) :
    ∀ γ ∈ GQ V, ∀ g, adel V dict mu P (γ * g) = adel V dict mu P g := by
  intro γ hγ g
  obtain ⟨γ', hγ', he⟩ := hd γ hγ g
  show mu (γ * g) * P (dict (γ * g)).1 (dict (γ * g)).2 = mu g * P (dict g).1 (dict g).2
  rw [he, hm.1, hm.2.2.1 γ hγ, one_mul]
  exact congrArg (mu g * ·) (hP g γ' hγ')

theorem adel_leftInv_of_chi {X : Comp → Data E r} (V : HSp D) (dict : GA D V → Σ k, Frame (X k).Ψ r)
    (mu : GA D V → ℂ) (la : ∀ k, Wt (X k).Ψ r) (P : FDSec X)
    (hd : ∀ γ ∈ GQ V, ∀ g, ∃ γ' ∈ (X (dict g).1).Γ, dict (γ * g) = ⟨(dict g).1, lact γ' (dict g).2⟩)
    (hdom : ∀ g, (dict g).2 ∈ (X (dict g).1).dom) (hm : MuUnit V dict mu)
    (hΓ : ∀ k, ∀ γ ∈ (X k).Γ, ∀ x ∈ (X k).dom, P k (lact γ x) = (X k).χ (la k) γ * P k x)
    (hχ : ∀ k, ∀ γ ∈ (X k).Γ, (X k).χ (la k) γ = 1) :
    ∀ γ ∈ GQ V, ∀ g, adel V dict mu P (γ * g) = adel V dict mu P g :=
  adel_leftInv_of_inv V dict mu P hd hm fun g γ' hγ' => by
    rw [hΓ _ γ' hγ' _ (hdom g), hχ _ γ' hγ', one_mul]

end Models

section Readings

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

def RdInvG (U : Unf Xo c σ r) : Prop :=
  ∀ a n, Dom a n → ∀ f ∈ sec Xo c a n, ∀ k, ∀ γ ∈ (U.X k).Γ, ∀ x ∈ (U.X k).dom,
    rdU U f k (lact γ x) = rdU U f k x

def SecGen (U : Unf Xo c σ r) : Prop :=
  ∀ a n, Dom a n → ∀ k, ∃ b m, Dom b m ∧
    (∃ f ∈ sec Xo c b m, ∃ x ∈ (U.X k).dom, rdU U f k x ≠ 0) ∧
    (∃ f ∈ sec Xo c (a + b) (n + m), ∃ x ∈ (U.X k).dom, rdU U f k x ≠ 0)

variable (U : Unf Xo c σ r)

theorem laU_add_even (a b : (E →+* ℂ) × ℕ → ℕ) (n m : ℕ) (hn : Even n) (hm : Even m) (k : U.Comp) :
    laU U (a + b) (n + m) k = laU U a n k + laU U b m k := by
  have h2 : (n + m) / 2 = n / 2 + m / 2 := by
    obtain ⟨x, rfl⟩ := hn
    obtain ⟨y, rfl⟩ := hm
    omega
  funext τ j
  simp only [laU, Pi.add_apply, h2]
  split_ifs <;> push_cast <;> ring

theorem Dom.add' {a b : (E →+* ℂ) × ℕ → ℕ} {n m : ℕ} (ha : Dom a n) (hb : Dom b m) : Dom (a + b) (n + m) :=
  ⟨fun τ _ _ hij => Nat.add_le_add (ha.1 τ hij) (hb.1 τ hij), ha.2.add hb.2⟩

theorem rdU_lact (hU : IsUnf U) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hdn : Dom a n) {f : Rul Xo c}
    (hf : f ∈ sec Xo c a n) (k : U.Comp) :
    ∀ γ ∈ (U.X k).Γ, ∀ x ∈ (U.X k).dom, rdU U f k (lact γ x) = (U.X k).χ (laU U a n k) γ * rdU U f k x :=
  (hU.2.2.2.2.1 a n hdn f hf k).2.2

theorem chi_eq_one_of_read (hU : IsUnf U) (hR : RdInvG U) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hdn : Dom a n)
    {f : Rul Xo c} (hf : f ∈ sec Xo c a n) {k : U.Comp} {γ : GL (Fin r) E} (hγ : γ ∈ (U.X k).Γ)
    {x : Frame (U.X k).Ψ r} (hx : x ∈ (U.X k).dom) (h0 : rdU U f k x ≠ 0) :
    (U.X k).χ (laU U a n k) γ = 1 := by
  have e1 := rdU_lact U hU hdn hf k γ hγ x hx
  rw [hR a n hdn f hf k γ hγ x hx] at e1
  have e2 : ((U.X k).χ (laU U a n k) γ - 1) * rdU U f k x = 0 := by
    rw [sub_mul, ← e1]; ring
  exact sub_eq_zero.1 ((mul_eq_zero.1 e2).resolve_right h0)

theorem chiTriv_of (hU : IsUnf U) (hR : RdInvG U) (hS : SecGen U) :
    ∀ a n, Dom a n → ∀ k, ∀ γ ∈ (U.X k).Γ, (U.X k).χ (laU U a n k) γ = 1 := by
  intro a n hdn k γ hγ
  obtain ⟨b, m, hbm, ⟨f1, hf1, x1, hx1, h1⟩, ⟨f2, hf2, x2, hx2, h2⟩⟩ := hS a n hdn k
  have e1 := chi_eq_one_of_read U hU hR hbm hf1 hγ hx1 h1
  have e2 := chi_eq_one_of_read U hU hR (Dom.add' hdn hbm) hf2 hγ hx2 h2
  rw [laU_add_even U a b n m hdn.2 hbm.2 k, (U.X k).χ_add _ _ γ hγ, e1, mul_one] at e2
  exact e2

theorem rdInvG_of_chi (hU : IsUnf U)
    (hχ : ∀ a n, Dom a n → ∀ k, ∀ γ ∈ (U.X k).Γ, (U.X k).χ (laU U a n k) γ = 1) : RdInvG U := by
  intro a n hdn f hf k γ hγ x hx
  rw [rdU_lact U hU hdn hf k γ hγ x hx, hχ a n hdn k γ hγ, one_mul]

variable {D : D7} (V : HSp D) (dict : GA D V → Σ k, Frame (U.X k).Ψ r) (mu : GA D V → ℂ)
  (Kf : Subgroup (GA D V)) (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hr : V.rank = r)

theorem rdU_leftInv (hU : IsUnf U) (hd : DictIsUnif V dict Kf th hr) (hm : MuUnit V dict mu)
    {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hdn : Dom a n)
    (hχ : ∀ k, ∀ γ ∈ (U.X k).Γ, (U.X k).χ (laU U a n k) γ = 1) {f : Rul Xo c} (hf : f ∈ sec Xo c a n) :
    ∀ γ ∈ GQ V, ∀ g, adel V dict mu (rdU U f) (γ * g) = adel V dict mu (rdU U f) g :=
  adel_leftInv_of_chi V dict mu (laU U a n) (rdU U f) hd.1 hd.2.2.2.1 hm (rdU_lact U hU hdn hf) hχ

theorem rdU_leftInv_of_rdInvG (hR : RdInvG U) (hd : DictIsUnif V dict Kf th hr) (hm : MuUnit V dict mu)
    {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hdn : Dom a n) {f : Rul Xo c} (hf : f ∈ sec Xo c a n) :
    ∀ γ ∈ GQ V, ∀ g, adel V dict mu (rdU U f) (γ * g) = adel V dict mu (rdU U f) g :=
  adel_leftInv_of_inv V dict mu (rdU U f) hd.1 hm fun g γ' hγ' => hR a n hdn f hf _ γ' hγ' _ (hd.2.2.2.1 g)

end Readings

namespace Core

variable {D : D7} (T : Core D)

theorem chiTriv_of_clauses (hunf : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → IsUnf (T.U j σ))
    (hR : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → RdInvG (T.U j σ))
    (hS : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → SecGen (T.U j σ)) :
    ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → ∀ a n, Dom a n → ∀ k, ∀ γ ∈ ((T.U j σ).X k).Γ,
      ((T.U j σ).X k).χ (laU (T.U j σ) a n k) γ = 1 :=
  fun j hj σ hσ => chiTriv_of (T.U j σ) (hunf j hj σ hσ) (hR j hj σ hσ) (hS j hj σ hσ)

theorem phiAd_leftInv_of_rdInvG {j : ℕ} {σ : T.Q.c.F →+* ℂ} (hR : RdInvG (T.U j σ))
    (hdU : ∃ th hr, (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧ DictIsUnif (T.V j σ) (T.dict j σ) (T.Kf j σ) th hr)
    (hm : MuUnit (T.V j σ) (T.dict j σ) (T.mu j σ)) {a : (D.host.E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hdn : Dom a n)
    {f : T.R j} (hf : f ∈ sec (T.Q.Xo j) T.Q.c a n) :
    ∀ γ ∈ GQ (T.V j σ), ∀ g, T.phiAd j σ a f (γ * g) = T.phiAd j σ a f g := by
  obtain ⟨th, hr, -, hd⟩ := hdU
  intro γ hγ g
  unfold phiAd
  simp only [Pi.smul_apply]
  rw [rdU_leftInv_of_rdInvG (T.U j σ) (T.V j σ) (T.dict j σ) (T.mu j σ) (T.Kf j σ) th hr hR hd hm hdn hf γ hγ g]

end Core

theorem LawsM.phiAd_leftInv {D : D7} {T : Core D} (h : LawsM T) {j : ℕ} (hj : InR D j) {σ : T.Q.c.F →+* ℂ}
    (hσ : GoodEmb T.Q.c σ) {a : (D.host.E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hdn : Dom a n) {f : T.R j}
    (hf : f ∈ sec (T.Q.Xo j) T.Q.c a n) :
    ∀ γ ∈ GQ (T.V j σ), ∀ g, T.phiAd j σ a f (γ * g) = T.phiAd j σ a f g :=
  T.phiAd_leftInv_of_rdInvG
    (rdInvG_of_chi (T.U j σ) (h.unf j hj σ hσ) (h.chiTriv j hj σ hσ)) (h.dictU j hj σ hσ)
    (h.muUnit j hj σ hσ) hdn hf

theorem LawsM.phiAd_leftInv_cusp {D : D7} {T : Core D} (h : LawsM T) {j : ℕ} (hj : InR D j)
    {σ : T.Q.c.F →+* ℂ} (hσ : GoodEmb T.Q.c σ) {a : (D.host.E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hdn : Dom a n)
    {f : T.R j} (hf : f ∈ T.cuspA j a n) :
    ∀ γ ∈ GQ (T.V j σ), ∀ g, T.phiAd j σ a f (γ * g) = T.phiAd j σ a f g :=
  h.phiAd_leftInv hj hσ hdn (cusp_le_sec (T.Q.Xo j) T.Q.c (T.U j) a n hf)

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.CoreExists
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open MeasureTheory
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def parameterOfRecord (D : D7) (hF : OFull D) (hz : OZeta D)
    (hDat : ∀ j, InR D j → ∃ hI : DatInt D j, DatLaws D j hI) (hN : N1ab) : Par D where
  H := hostOf D (unramBridge D.host.E (cmUnram_conj D))
  l := levelG D (hU := unramBridge D.host.E (cmUnram_conj D))
  c := coeffFieldOfRecord D (hU := unramBridge D.host.E (cmUnram_conj D)) hz
  Dw := datumAtLift D (unramBridge D.host.E (cmUnram_conj D)) hDat
  Xo := fun j => Classical.choice (hN D.host.E (hostOf D (unramBridge D.host.E (cmUnram_conj D)))
    (datumAtLift D (unramBridge D.host.E (cmUnram_conj D)) hDat j) (levelG D (hU := unramBridge D.host.E (cmUnram_conj D)))
    (datumAtLift_pq_pos D (unramBridge D.host.E (cmUnram_conj D)) hDat j))
  eO := eOf D hF

theorem parameter_record_conditions (D : D7) (hF : OFull D) (hz : OZeta D)
    (hDat : ∀ j, InR D j → ∃ hI : DatInt D j, DatLaws D j hI) (hN : N1ab) : (parameterOfRecord D hF hz hDat hN).Pins := by
  refine ⟨⟨rfl, rfl, rfl, tauEmb_sqrt D⟩, levelG_M D _, eOf_spec D hF, fun j hj => ?_⟩
  show IsDatW D j (datumAtLift D (unramBridge D.host.E (cmUnram_conj D)) hDat j)
  unfold datumAtLift
  rw [dif_pos hj]
  exact isDatW_datumOf D _ j _ _

theorem parameter_record_pq_pos (D : D7) (hF : OFull D) (hz : OZeta D)
    (hDat : ∀ j, InR D j → ∃ hI : DatInt D j, DatLaws D j hI) (hN : N1ab) (j : ℕ) :
    1 ≤ ((parameterOfRecord D hF hz hDat hN).Dw j).p + ((parameterOfRecord D hF hz hDat hN).Dw j).q :=
  datumAtLift_pq_pos D _ hDat j

variable {D : D7}

def levSet (V : HSp D) (N : ℕ) : Set (GA D V) :=
  {k | k ∈ GfC V ∧ ∀ z ∈ latHat V, ∃ y ∈ latHat V, (finHom V k).1.mulVec z - z = N • y}

def kfW (V : HSp D) (N : ℕ) : Subgroup (GA D V) := Subgroup.closure (levSet V N)

def LevGrp (V : HSp D) (N : ℕ) : Prop := ∀ k ∈ kfW V N, k ∈ levSet V N

theorem isLevelK_kfW {V : HSp D} {N : ℕ} (h : LevGrp V N) : IsLevelK V N (kfW V N) :=
  fun k => ⟨fun hk => h k hk, fun hk => Subgroup.subset_closure hk⟩

section One

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

def RdIndep1 (U : Unf Xo c σ r) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (k : ℕ), Dom a k → ∀ (n : ℕ) (b : Fin n → Rul Xo c), (∀ i, b i ∈ sec Xo c a k) →
    LinearIndependent c.F b → LinearIndependent ℂ (fun i => rdU U (b i))

def HolFD1 (U : Unf Xo c σ r) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → FiniteDimensional ℂ (holSub U.X (laU U a n))

def RdDomInj1 (U : Unf Xo c σ r) : Prop :=
  ∀ a n, Dom a n → ∀ f ∈ sec Xo c a n, rdU U f ∈ holSub U.X (laU U a n) →
    (∀ k, ∀ x ∈ (U.X k).dom, rdU U f k x = 0) → f = 0

def AdelMeas1 (U : Unf Xo c σ r) (V : HSp D) (dict : GA D V → Σ k, Frame (U.X k).Ψ r) (mu : GA D V → ℂ) : Prop :=
  ∀ (la : ∀ k, Wt (U.X k).Ψ r) (P : FDSec U.X), IsHolCusp U.X la P →
    AEStronglyMeasurable (onQ V (adel V dict mu P)) (muQ1 V)

def AeDom1 (U : Unf Xo c σ r) (V : HSp D) (dict : GA D V → Σ k, Frame (U.X k).Ψ r) (mu : GA D V → ℂ) : Prop :=
  ∀ (la : ∀ k, Wt (U.X k).Ψ r) (P : FDSec U.X), P ∈ holSub U.X la →
    onQ V (adel V dict mu P) =ᵐ[muQ1 V] 0 → ∀ k, ∀ x ∈ (U.X k).dom, P k x = 0

end One

abbrev PkgT (Q : Par D) (j : ℕ) (σ : Q.c.F →+* ℂ) : Type 1 :=
  Σ U : Unf (Q.Xo j) Q.c σ D.R.r, (GA D (D.sp.W j) → Σ k, Frame (U.X k).Ψ D.R.r) × (GA D (D.sp.W j) → ℂ)

structure PkgOK (Q : Par D) (j : ℕ) (σ : Q.c.F →+* ℂ) (U : Unf (Q.Xo j) Q.c σ D.R.r)
    (dict : GA D (D.sp.W j) → Σ k, Frame (U.X k).Ψ D.R.r) (mu : GA D (D.sp.W j) → ℂ) : Prop where

  unf : IsUnf U

  unTest : ∀ k x, FromTest (K := Q.c.F) (fun S _ _ => FrPt (Q.Xo j) Q.c S) (fun φ y z => FrMap φ y z) (U.un k x)

  chiTriv : ∀ a n, Dom a n → ∀ k, ∀ γ ∈ (U.X k).Γ, (U.X k).χ (laU U a n k) γ = 1

  dictU : ∃ th hr, (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧
    DictIsUnif (D.sp.W j) dict (kfW (D.sp.W j) (D.host.g 0 * D.host.g 1)) th hr

  xiAbs : ∀ k (τ : D.host.E →+* ℂ), ‖τ (U.X k).ξ0‖ = xiR D

  muUnit : MuUnit (D.sp.W j) dict mu
  muCont : Continuous mu

  rdIndep : RdIndep1 U
  holFD : HolFD1 U

  rdDomInj : RdDomInj1 U

  adelMeas : AdelMeas1 U (D.sp.W j) dict mu

  aeDom : AeDom1 U (D.sp.W j) dict mu

  latZ : FJ.LatZ U.X (WeightFamilies.rho D j)
  cuNe : FJ.CuNeF U.X (WeightFamilies.rho D j)
  expo : FJ.ExpoMatch U.X 1 (WeightFamilies.rho D j) (D.host.g 0 * D.host.g 1)

def FamOK (Q : Par D) (j : ℕ) (σ : Q.c.F →+* ℂ) : Prop :=
  ∀ (g : ℕ) (ty : Fin g → (D.host.E →+* ℂ)), IsTypeFn Q.H (Q.Dw j).p (Q.Dw j).q ty →
    Nonempty (FamilyUnif (Q.Xo j) (σ.comp (IntermediateField.inclusion Q.c.le).toRingHom) ty)

def HalfPb (Q : Par D) : Prop :=
  ∃ pb : Fin 2 → HeightOneSpectrum (𝓞 D.host.K), (∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ (pb k).asIdeal) ∧
    Q.l.Mb = ∏ k, (pb k).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))

structure LawsRest (Q : Par D) : Prop where

  evalWD : ∀ j, InR D j → EvalWD (K := Q.c.F) (fun S _ _ => FrPt (Q.Xo j) Q.c S) (fun φ y z => FrMap φ y z)

  wtField : ∀ j, InR D j → WtField (Q.Xo j) Q.c
  intDiagUnit : ∀ j, InR D j → IntDiagUnit (Q.Xo j) Q.c

  algPtLa : ∀ j, InR D j → AlgPtLa (Q.Xo j) Q.c
  intFrExt : ∀ j, InR D j → IntFrExt (Q.Xo j) Q.c

  m5 : SiegelSpaceAlgebra (E := D.host.E)

  volTie : VolTieG D

  levGrp : ∀ j, InR D j → LevGrp (D.sp.W j) (D.host.g 0 * D.host.g 1)

  half : HalfPb Q

  pkg : ∀ j, InR D j → ∀ σ, GoodEmb Q.c σ → FamOK Q j σ → ∃ U dict mu, PkgOK Q j σ U dict mu

  dataAll : ∀ j σ, Nonempty (PkgT Q j σ)

section Build

variable {Q : Par D}

theorem pkgEx (hRs : LawsRest Q) (hfam : ∀ j, InR D j → ∀ σ, GoodEmb Q.c σ → FamOK Q j σ) (j : ℕ)
    (σ : Q.c.F →+* ℂ) : ∃ p : PkgT Q j σ, InR D j → GoodEmb Q.c σ → PkgOK Q j σ p.1 p.2.1 p.2.2 := by
  by_cases hj : InR D j
  · by_cases hσ : GoodEmb Q.c σ
    · obtain ⟨U, dict, mu, h⟩ := hRs.pkg j hj σ hσ (hfam j hj σ hσ)
      exact ⟨⟨U, dict, mu⟩, fun _ _ => h⟩
    · exact ⟨Classical.choice (hRs.dataAll j σ), fun _ h => absurd h hσ⟩
  · exact ⟨Classical.choice (hRs.dataAll j σ), fun h => absurd h hj⟩

def pkgOf (hRs : LawsRest Q) (hfam : ∀ j, InR D j → ∀ σ, GoodEmb Q.c σ → FamOK Q j σ) (j : ℕ)
    (σ : Q.c.F →+* ℂ) : PkgT Q j σ := (pkgEx hRs hfam j σ).choose

def coreOf (hRs : LawsRest Q) (hfam : ∀ j, InR D j → ∀ σ, GoodEmb Q.c σ → FamOK Q j σ) : Core D where
  Q := Q
  U j σ := (pkgOf hRs hfam j σ).1
  V j _ := D.sp.W j
  dict j σ := (pkgOf hRs hfam j σ).2.1
  mu j σ := (pkgOf hRs hfam j σ).2.2
  Kf j _ := kfW (D.sp.W j) (D.host.g 0 * D.host.g 1)
  pb := hRs.half.choose

end Build

theorem datHolds (D : D7) : ∀ j, InR D j → ∃ hI : DatInt D j, DatLaws D j hI :=
  fun j hj => ⟨datInt_holds D j,
    { unimod := efW_unimod_holds D j _, rank := latW_rank D j hj, dom := datDom_holds D j hj _ }⟩

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.DepLaws
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions

variable {D : D7}

structure LawsPi (T : Core D) (Dd : DepData D.host.E) : Prop where

  page : Dd.Q.g1 = D.host.g 0 ∧ Dd.Q.g2 = D.host.g 1 ∧ Dd.Q.q1 = D.host.q ∧ Dd.Q.dd = D.host.d ∧ Dd.Q.f = D.R.f ∧
    Dd.Q.r = D.R.r
  tPos : TPos Dd

  sm : Dd.Q.sm = D.host.small

  wts : ∀ j, InR D j → (∀ τ, Antitone fun i => Dd.aL j (τ, i)) ∧ 2 * D.R.f * D.R.r ≤ Dd.nW j

  piSplit : PiSplit (H := T.Q.H) Dd
  piHalf : PiHalf T.Q.l Dd

structure LawsDep (T : Core D) [StarRing (𝓞 D.host.E)] : Prop where

  star_eq : ∀ a : 𝓞 D.host.E, star a = T.Q.H.bar a

  chartEx : ∀ j, InR D j → IntChartEx (T.Q.Xo j) T.Q.c
  chartIndep : ∀ j, InR D j → ChartIndep (T.Q.Xo j) T.Q.c

def NuFinAt (T : Core D) (Dd : DepData D.host.E) [StarRing (𝓞 D.host.E)] : Prop :=
  ∀ j, InR D j → ∀ la : HeightOneSpectrum (𝓞 T.Q.c.F), nuWAt (Xo := T.Q.Xo j) Dd la j ≠ ⊤

def nuE (T : Core D) (Dd : DepData D.host.E) [StarRing (𝓞 D.host.E)] (j : ℕ) (la : HeightOneSpectrum (𝓞 T.Q.c.F)) :
    ENNReal :=
  (nuWAt (Xo := T.Q.Xo j) Dd la j).toENNReal

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.FreeBridgeU
section
noncomputable section

namespace Formalism.L2.PjFree

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor

open Formalism.L2.Pj (Rul)

theorem isNormOn_iff {K : Type} [Field K] {R : Type} [CommRing R] [Algebra K R] (C : Submodule K R)
    (σ : K →+* ℂ) (N : R → ℝ) : PjFree.IsNormOn C σ N ↔ Formalism.L2.Pj.IsNormOn C σ N :=
  ⟨fun h => ⟨h.1, h.2, h.3, h.4⟩, fun h => ⟨h.1, h.2, h.3, h.4⟩⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) (c : Coeff l)

theorem trivCls_eq : PjFree.trivCls Xo c = Formalism.L2.Pj.trivCls Xo c := rfl

variable {Xo c}

def QPt.toPj (q : PjFree.QPt Xo c) : Formalism.L2.Pj.QPt Xo c := ⟨q.T, q.ι, q.y, q.triv⟩

def QPt.ofPj (q : Formalism.L2.Pj.QPt Xo c) : PjFree.QPt Xo c := ⟨q.T, q.ι, q.y, q.triv⟩

theorem QPt.ofPj_toPj (q : PjFree.QPt Xo c) : QPt.ofPj q.toPj = q := rfl

theorem QPt.toPj_ofPj (q : Formalism.L2.Pj.QPt Xo c) : (QPt.ofPj q).toPj = q := rfl

theorem ordQ_toPj (q : PjFree.QPt Xo c) (f : Rul Xo c) :
    Formalism.L2.Pj.ordQ Xo c q.toPj f = PjFree.ordQ Xo c q f := rfl

variable (Xo c)

theorem valSet_alg_eq (la : HeightOneSpectrum (𝓞 c.F)) :
    PjFree.valSet Xo c (PjFree.algCls Xo c) la = Formalism.L2.Pj.valSet Xo c (Formalism.L2.Pj.algCls Xo c) la := rfl

theorem regR1Q_iff_free (C : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c)) :
    PjFree.RegularityR1Quotient Xo c C ↔ Formalism.L2.Pj.RegularityR1Quotient Xo c C :=
  ⟨fun h a n f hf hx q => h a n f hf hx (QPt.ofPj q), fun h a n f hf hx q => h a n f hf hx q.toPj⟩

theorem regR2Q_iff_free (C : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c)) :
    PjFree.RegularityR2Quotient Xo c C ↔ Formalism.L2.Pj.RegularityR2Quotient Xo c C :=
  ⟨fun h aL nL aE nE k ws et c' hc hw he hx q => h aL nL aE nE k ws et c' hc hw he hx (QPt.ofPj q),
   fun h aL nL aE nE k ws et c' hc hw he hx q => h aL nL aE nE k ws et c' hc hw he hx q.toPj⟩

theorem intAll_iff : PjFree.IntAll Xo c ↔ Formalism.L2.Pj.IntAll Xo c := Iff.rfl

theorem nabUniq_iff : PjFree.NabUniq Xo c ↔ Formalism.L2.Pj.NabUniq Xo c := Iff.rfl

theorem frBaseChg_eq : @PjFree.FrBaseChg = @Formalism.L2.Pj.FrBaseChg := rfl

theorem reFrame_eq : @PjFree.ReFrame = @Formalism.L2.Pj.ReFrame := rfl

theorem xoNumPt_eq : @PjFree.XoNumPt = @Formalism.L2.Pj.XoNumPt := rfl

theorem locFld_eq : @PjFree.LocFld = @Formalism.L2.Pj.LocFld := rfl

theorem tanLin_eq : @PjFree.TanLin = @Formalism.L2.Pj.TanLin := rfl

theorem sClause_eq : @PjFree.SClause = @Formalism.L2.Pj.SClause := rfl

theorem intRebase_eq : @PjFree.IntRebase = @Formalism.L2.Pj.IntRebase := rfl

end Formalism.L2.PjFree
end
end

