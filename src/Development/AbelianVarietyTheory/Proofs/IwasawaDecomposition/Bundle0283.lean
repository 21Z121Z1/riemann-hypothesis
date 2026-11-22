import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSplittingCharacterSelf
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0136
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EquivariantOfWave
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0138
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntValuationEqOfMem
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0073
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import ReciprocityTheory.NeutralLocalFields.Reciprocity
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
import Formalism.LocalToGlobal.HermitianForms.Bundle0006
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanRangeMulVec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0119
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionStar
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasEigEigOfType
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows

noncomputable section

namespace GlobalTheory.Mem.R3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def eigOfType (R : RealDat3 D A3 Ks) (F : Face3 D A3) {X0 : BaseLevelRowSide D} (Y : Read (A3 := A3) R.toRealDat F.lv2 X0)
    (π : D.what₂.FT) : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ :=
  principalLevelFrame.cOfT (Y.PW ⟨0, Y.hm⟩)
    (levS _ (R.βW ⟨0, Y.hm⟩) (R.datWp ⟨0, Y.hm⟩ (R.toRealDat.levL F.lv2 false (sg0 D A3.A))))
    (levChi _ (R.βW ⟨0, Y.hm⟩) (R.datWp ⟨0, Y.hm⟩ (R.toRealDat.levL F.lv2 false (sg0 D A3.A))))
    (SsetF R.toRealDat (Y.tupT D.what₂.mu0)) (principalLevelFrame.rowRepR R.θ (Y.eFT π))

def HasEig (R : RealDat3 D A3 Ks) (F : Face3 D A3) {X0 : BaseLevelRowSide D} (Y : Read (A3 := A3) R.toRealDat F.lv2 X0)
    (π : D.what₂.FT) (c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ) : Prop :=
  principalLevelFrame.IsEigOf (Y.PW ⟨0, Y.hm⟩)
    (levS _ (R.βW ⟨0, Y.hm⟩) (R.datWp ⟨0, Y.hm⟩ (R.toRealDat.levL F.lv2 false (sg0 D A3.A))))
    (levChi _ (R.βW ⟨0, Y.hm⟩) (R.datWp ⟨0, Y.hm⟩ (R.toRealDat.levL F.lv2 false (sg0 D A3.A))))
    (SsetF R.toRealDat (Y.tupT D.what₂.mu0)) (principalLevelFrame.rowRepR R.θ (Y.eFT π)) c

theorem hasEig_eigOfType {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}
    {Y : Read (A3 := A3) R.toRealDat F.lv2 X0} {π : D.what₂.FT} (h : ∃ c, HasEig R F Y π c) :
    HasEig R F Y π (eigOfType R F Y π) := by
  unfold eigOfType principalLevelFrame.cOfT
  unfold HasEig at h ⊢
  rw [dif_pos h]
  exact h.choose_spec

end GlobalTheory.Mem.R3

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasInfExpIffHasInfQ
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeckeInfExp

set_option maxHeartbeats 1000000 in
open GlobalTheory.FockCompare GlobalTheory.HeckeFinTrivial in

theorem hasInfQ_of_hasInfExp (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (e : D.what₂.Tau → ℚ)
    (hc : ChrEq c χ) (h : ∀ τ, HasInfExp D c τ (e τ)) : χ.HasInfQ (tauE D) e := by
  classical
  choose n hn hx using h
  refine ⟨n, hn, fun k => ?_⟩
  obtain ⟨⟨θ', hθ'⟩, -⟩ := GlobalTheory.Member.infiniteAdele_bijective D
  obtain ⟨θ, hθ⟩ : ∃ θ : GlobalTheory.Mem.Th.InfF D, IsInfFam θ := ⟨fun τ => θ' (tauE D τ), fun τ => hθ' _⟩
  obtain ⟨ρ, hρ, r1, r0⟩ := exists_real_chart D θ hθ (GlobalTheory.CMTypePlaces.places_bijective D)
  obtain ⟨s, hs⟩ := RealChart.exists_chart D θ hθ ρ hρ r1 r0
  obtain ⟨-, a, b, -, -, hab, ha, hb⟩ := GlobalTheory.IdeleParts.congr_open_and_parts D
  have ext : ∀ a b : AE D, finPart D a = finPart D b → (∀ τ, θ τ (infPart D a) = θ τ (infPart D b)) → a = b := by
    intro a b h1 h2
    rw [← sub_eq_zero]
    exact hs.ext _ (by rw [RingHom.map_sub, h1, sub_self]) fun τ => by
      rw [RingHom.map_sub, RingHom.map_sub, h2, sub_self]
  let t : (D.what₂.Tau → ℂˣ) → AE D := fun z => s (fun τ => (z τ : ℂ)) + (1 - s 1)
  have tf : ∀ z, finPart D (t z) = 1 := fun z => by
    simp only [t, RingHom.map_add, RingHom.map_sub, RingHom.map_one, hs.fin, zero_add, sub_zero]
  have ti : ∀ z τ, θ τ (infPart D (t z)) = z τ := fun z τ => by
    simp only [t, RingHom.map_add, RingHom.map_sub, RingHom.map_one, hs.comp, Pi.one_apply, sub_self, add_zero]
  let T : (D.what₂.Tau → ℂˣ) →* AE D :=
    { toFun := t
      map_one' := ext _ _ (by rw [tf, RingHom.map_one]) fun τ => by
        rw [ti, RingHom.map_one, RingHom.map_one]; rfl
      map_mul' := fun x y => ext _ _ (by rw [RingHom.map_mul, tf, tf, tf, mul_one]) fun τ => by
        rw [RingHom.map_mul, RingHom.map_mul, ti, ti, ti]; rfl }
  have hT : ∀ x : (AE D)ˣ, finPart D (x : AE D) = 1 →
      x = T.toHomUnits fun τ => Units.map ((θ τ).comp (infPart D)).toMonoidHom x := fun x hx =>
    Units.ext (ext _ _ (hx.trans (tf _).symm) fun τ =>
      (ti (fun τ => Units.map ((θ τ).comp (infPart D)).toMonoidHom x) τ).symm)
  have key : ∀ z : D.what₂.Tau → ℂˣ,
      ((c (T.toHomUnits z) : Circle) : ℂ) = ∏ τ, ((z τ : ℂ) / ((‖(z τ : ℂ)‖ : ℝ) : ℂ)) ^ n τ := by
    intro z
    have h1 : c (T.toHomUnits z) = ∏ τ, c (T.toHomUnits (Pi.mulSingle τ (z τ))) := by
      conv_lhs => rw [← Finset.univ_prod_mulSingle z]
      rw [map_prod, map_prod]
    have h2 := congrArg Circle.coeHom h1
    rw [map_prod] at h2
    refine h2.trans (Finset.prod_congr rfl fun τ _ => ?_)
    have h3 := (hx τ).2 θ hθ (T.toHomUnits (Pi.mulSingle τ (z τ))) (tf _) fun τ' hτ' =>
      (ti _ τ').trans (by rw [Pi.mulSingle_eq_of_ne hτ', Units.val_one])
    have h4 : θ τ (infPart D ((T.toHomUnits (Pi.mulSingle τ (z τ)) : (AE D)ˣ) : AE D)) = z τ :=
      (ti _ τ).trans (by rw [Pi.mulSingle_eq_same])
    rw [h4] at h3
    exact h3
  rw [← eq_inf D c χ hc k _ _ (hab _) (hb _).1 (hb _).2, hT _ (ha (Units.map (incA D).toMonoidHom k)).2, key]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have h5 : ((Units.map ((θ τ).comp (infPart D)).toMonoidHom (a (Units.map (incA D).toMonoidHom k)) : ℂˣ) : ℂ) =
      tauE D τ (k : D.host.E) :=
    (congrArg (θ τ) (ha (Units.map (incA D).toMonoidHom k)).1).trans ((hθ τ).1 k)
  rw [h5]

theorem hasInfExp_iff_hasInfQ : ∀ (D : D7) (c : GlobalTheory.Mem.Th.IdC D) (χ : Formalism.L2.Host.HChar D.host.E) (a : D.what₂.Tau → ℚ),
    Formalism.IndefR.Links.ChrEq c χ → ((∀ τ, HasInfExp D c τ (a τ)) ↔ χ.HasInfQ (Formalism.L2.Host.embTau D) a) :=
  fun D c χ a hc => ⟨hasInfQ_of_hasInfExp D c χ a hc, hasInfExp_of_chrEq D c χ a hc⟩

end GlobalTheory.HeckeInfExp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasInfExpMulZero
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Lev Formalism.IndefR.Cx GlobalTheory.Chain NumberField
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.InnerSteps

variable {D : D7}

theorem hasInfQ_tauE {χ : Formalism.L2.Host.HChar D.host.E} {a : D.R.Psi → ℚ}
    (h : χ.HasInfQ (Formalism.L2.Host.embPsi D.host) a) : χ.HasInfQ (tauE D) fun τ => a (D.eTau τ) := by
  obtain ⟨n, hn, h⟩ := h
  refine ⟨fun τ => n (D.eTau τ), fun τ => hn _, fun k => ?_⟩
  rw [h k]
  exact (Equiv.prod_comp D.eTau (fun g => (Formalism.L2.Host.embPsi D.host g (k : D.host.E) /
      ((‖Formalism.L2.Host.embPsi D.host g (k : D.host.E)‖ : ℝ) : ℂ)) ^ n g)).symm

theorem hasInfExp_mul_zero {χ η : (AE D)ˣ →* Circle} {τ : D.what₂.Tau} {a : ℚ} (hχ : HasInfExp D χ τ a)
    (hη : HasInfExp D η τ 0) : HasInfExp D (χ * η) τ a := by
  obtain ⟨n, hn, h1, h2⟩ := hχ
  obtain ⟨m, hm, -, h3⟩ := hη
  have hm0 : m = 0 := by exact_mod_cast hm.trans (mul_zero _)
  refine ⟨n, hn, h1, fun θ hθ x hx hτ => ?_⟩
  rw [MonoidHom.mul_apply, Circle.coe_mul, h2 θ hθ x hx hτ, h3 θ hθ x hx hτ, hm0, zpow_zero, mul_one]

theorem exp_chrStep {T0 : Type} (L : LevCh D T0) {μ0 : T0} (hL : L.Is μ0) (t : T0) (k : Fin D.R.m) (τ : D.what₂.Tau) :
    HasInfExp D (Lift.chrStep (L.mu t) L.eta ((k : ℕ) + 1)).1 τ (expS D k τ) ∧
      HasInfExp D (Lift.chrStep (L.mu t) L.eta ((k : ℕ) + 1)).2 τ (expT D k τ) := by
  have h1 := GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ (hL.mu0 k) (hasInfQ_tauE (L.C.isMu0 k).inf) τ
  simp only [Formalism.L2.Host.eExp, Equiv.symm_apply_apply] at h1
  have h2 := GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ hL.eta
    (hasInfQ_tauE (a := fun _ => 1 / 2) ⟨fun _ => 1, fun _ => by norm_num, L.C.isEta.inf⟩) τ
  obtain ⟨n, hn, ho⟩ := hL.xi_fin t
  haveI : IsTotallyComplex D.host.E := by infer_instance
  have h3 := GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ (fun _ => 0) (hL.xi t)
    ⟨fun _ => 0, fun _ => by norm_num, fun x => by
      rw [GlobalTheory.TypeValues.inf_eq_one _ hn ho x]; simp⟩ τ
  have h4 : HasInfExp D (L.mu t ((k : ℕ) + 1)) τ (-(D.hc τ).e k) := hasInfExp_mul_zero h1 h3
  unfold Lift.chrStep
  by_cases hk : Even (k : ℕ)
  · rw [if_pos hk.add_one, (exp_of_even hk τ).1, (exp_of_even hk τ).2]
    exact ⟨hasInfExp_div h4 h2, h4⟩
  · rw [if_neg (fun h => hk (by simpa [Nat.odd_add_one, Nat.not_odd_iff_even] using h)), (exp_of_odd hk τ).1,
      (exp_of_odd hk τ).2]
    exact ⟨h4, hasInfExp_div h4 h2⟩

theorem toEAf_surjective : Function.Surjective (toEAf D) := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, RingHom.map_zero _⟩
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, RingHom.map_add _ _ _⟩
  | tmul x a => exact ⟨pairA D.host.F 0 a ⊗ₜ[D.host.F] x, rfl⟩

theorem sum_mul_idem {R ι : Type} [CommRing R] (p : ι → R) (s : Finset ι) (h : ∀ i ∈ s, p i * p i = p i)
    (h0 : ∀ i ∈ s, ∀ j ∈ s, j ≠ i → p i * p j = 0) {i : ι} (hi : i ∈ s) : p i * (∑ i ∈ s, p i) = p i := by
  rw [Finset.mul_sum, Finset.sum_eq_single i (fun j hj hji => h0 i hi j hj hji) (fun h => absurd hi h), h i hi]

theorem resS_idemSum {e : AE D} {P : Finset (Pl D.host.E)} (h : IsIdemSum e P) :
    ∃ hi : toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, ∀ PP ∈ P, resS D.host.F PP ⟨toEAf D e, hi⟩ = 1 := by
  have he := GlobalTheory.PlaceDatum.idemSum_mul_self h
  have hint : toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    GlobalTheory.IdemRes.toEAf_mem_of_finPart (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, he]))
  refine ⟨hint, fun PP hP => ?_⟩
  obtain ⟨⟨es, hes, hsum⟩, hc⟩ := h
  have h1 : ∀ i ∈ P, es i * es i = es i := fun i hi => (hes i hi).1.1
  have hcross : ∀ i ∈ P, ∀ j ∈ P, es i * cA D (es j) = 0 :=
    GlobalTheory.PlaceDatum.cross_eq_zero (R := AE D) GlobalTheory.PlaceDatum.isUnit_natCast (cA D) es P h1 (hsum ▸ hc)
  have h2 : ∀ i ∈ P, ∀ j ∈ P, j ≠ i → es i * es j = 0 := fun i hi j hj hji =>
    GlobalTheory.PlaceDatum.idemAt_mul (hes i hi) (hes j hj) (hcross i hi j hj) (hcross j hj i hi) hji
  have h3 : es PP * e = es PP := by
    rw [hsum]; exact sum_mul_idem (R := AE D) es P h1 h2 hP
  obtain ⟨h4, h5⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D (es PP) PP (hes PP hP)
  have h6 : (⟨_, h4⟩ * ⟨_, hint⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = ⟨_, h4⟩ :=
    Subtype.ext (by change toEAf D _ * toEAf D _ = toEAf D _; rw [← RingHom.map_mul, h3])
  have h7 := congrArg (resS D.host.F PP) h6
  rwa [map_mul, h5, one_mul] at h7

def rect (κ : Type) [Zero κ] [One κ] (b a : ℕ) : Matrix (Fin b) (Fin a) κ := fun i j => if i.val = j.val then 1 else 0

theorem lowZero_rect {κ : Type} [Zero κ] [One κ] (b a k : ℕ) : LowZero k (rect κ b a) :=
  fun i j hi hj => if_neg (by omega)

theorem topL_rect {κ : Type} [Zero κ] [One κ] {b a k : ℕ} (hb : k ≤ b) (ha : k ≤ a) : topL k (rect κ b a) = 1 := by
  ext i j
  unfold topL rect
  rw [dif_pos ⟨lt_of_lt_of_le i.2 hb, lt_of_lt_of_le j.2 ha⟩, Matrix.one_apply]
  simp only [Fin.ext_iff]

theorem frame_smul {R : Type} [CommRing R] {a b : ℕ} (p : GL (Fin a) R) (q : GL (Fin b) R) (c : R)
    (y z : Matrix (Fin b) (Fin a) R) (h : ∀ i j, z i j = c * (q.val * y * (p⁻¹).val) i j) (i : Fin b) (j : Fin a) :
    ((q⁻¹).val * z * p.val) i j = c * y i j := by
  have hz : z = c • (q.val * y * (p⁻¹).val) := Matrix.ext h
  rw [hz, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc q.val, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul,
    Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one, Matrix.smul_apply, smul_eq_mul]

theorem exists_rect (S T : HSp D) (βS : GL (Fin S.rank) (Datum.EAf D)) (βT : GL (Fin T.rank) (Datum.EAf D))
    {e : AE D} {P : Finset (Pl D.host.E)} (h : IsIdemSum e P) :
    ∃ x : WO S T, IsHalf e x ∧ IsIntM (frMapO S T βS βT x) ∧
      ∀ PP ∈ P, redM PP (frMapO S T βS βT x) = rect _ _ _ := by
  obtain ⟨hi, hr⟩ := resS_idemSum h
  have he := GlobalTheory.PlaceDatum.idemSum_mul_self h
  choose s hs using toEAf_surjective (D := D)
  let x : Matrix (Fin T.rank) (Fin S.rank) (AE D) :=
    fun i j => e * s (HMul.hMul (HMul.hMul βT.val (rect (Datum.EAf D) T.rank S.rank)) (βS⁻¹).val i j)
  have hf : ∀ i j, frMapO S T βS βT x i j = if i.val = j.val then toEAf D e else 0 := by
    intro i j
    refine (frame_smul βS βT (toEAf D e) (rect (Datum.EAf D) T.rank S.rank) (x.map (toEAf D)) (fun i j => ?_) i j).trans ?_
    · exact (RingHom.map_mul _ _ _).trans (congrArg _ (hs _))
    · rw [rect, mul_ite, mul_one, mul_zero]
  have hI : IsIntM (frMapO S T βS βT x) := fun i j => by
    rw [hf]
    split_ifs
    · exact hi
    · exact zero_mem _
  refine ⟨x, fun i j => by simp only [x]; rw [← mul_assoc, he], hI, fun PP hP => ?_⟩
  ext i j
  refine (dif_pos (hI i j)).trans ?_
  unfold rect
  split_ifs with hij
  · rw [← hr PP hP]
    exact congrArg _ (Subtype.ext ((hf i j).trans (if_pos hij)))
  · rw [← map_zero (resS D.host.F PP)]
    exact congrArg _ (Subtype.ext ((hf i j).trans (if_neg hij)))

theorem omegaG_ne_zero {a b : ℕ} (hab : a ≤ b) (L : LevDat D.host.E ℂ a) (χ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)) (hy : ∀ PP ∈ L.Pg, y PP = rect _ _ _) :
    omegaG L χ y ≠ 0 := by
  unfold omegaG
  split_ifs with h
  · refine mul_ne_zero (mul_ne_zero (Units.ne_zero _) ?_) ?_
    · exact Finset.prod_ne_zero_iff.2 fun _ _ => Finset.prod_ne_zero_iff.2 fun _ _ => Units.ne_zero _
    · exact Finset.prod_ne_zero_iff.2 fun _ _ => inv_ne_zero (Units.ne_zero _)
  · refine absurd ⟨fun PP hP => ?_, fun _ => 1, fun PP => ?_, fun _ => one_mem _, ?_⟩ h
    · rw [hy PP hP]; exact lowZero_rect _ _ _
    · rw [hy PP.1 PP.2, topL_rect hab le_rfl, Units.val_one]
    · convert L.P.H.one_mem using 1
      funext PP
      exact blockDiagonalExtendByOnePrimeField_one _ _

theorem omegaQ_ne_zero {a b r : ℕ} (ha : r ≤ a) (hb : r ≤ b) (Q : Finset (Pl D.host.E))
    (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (k : ℤ)
    (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)) (hy : ∀ PP ∈ Q, y PP = rect _ _ _) :
    omegaQ Q r ξ k y ≠ 0 := by
  unfold omegaQ
  split_ifs with h
  · exact Finset.prod_ne_zero_iff.2 fun _ _ => zpow_ne_zero _ (Units.ne_zero _)
  · refine absurd (fun PP hP => ?_) h
    rw [hy PP hP, topL_rect hb ha, Matrix.det_one]
    exact ⟨lowZero_rect _ _ _, isUnit_one⟩

theorem stepVec_vac {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    {βS : GL (Fin S.rank) (Datum.EAf D)} {βT : GL (Fin T.rank) (Datum.EAf D)} {L : LevDat D.host.E ℂ S.rank}
    {χ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ} {Q : Finset (Pl D.host.E)}
    {ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ} {f₀ f : WO S T → ℂ} (dS : IsSelfDualC S ΛS) (dT : IsSelfDualC T ΛT)
    (hr : S.rank ≤ T.rank) (h : IsStepVecOf ψ θ S T sS sT ΛS ΛT βS βT L χ Q ξ f₀ f) :
    IsThetaFunO ψ S T f ∧ f ≠ 0 ∧ ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f := by
  classical
  obtain ⟨hv, e, he', ⟨Tm, hTm⟩, hall⟩ := h
  obtain ⟨P, he, hP⟩ : ∃ P, IsIdemSum e P ∧ ∀ PP, PP ∈ P ↔ PP ∈ L.Pg ∨ PP ∈ Q :=
    ⟨_, he', fun PP => Finset.mem_union⟩
  have h0 : f₀ ≠ 0 := by
    rintro rfl
    obtain ⟨⟨p, hp⟩, h2⟩ := hv.2.norm
    have := h2 p hp
    simp [nrm2] at this
  have hinf := GlobalTheory.PlaceDatum.infPart_idemSum he
  obtain ⟨K, hK, hC⟩ := GlobalTheory.PlaceDatum.exists_nsmul_of_frMapO dS.1 dT.1 βS βT
  have hSB := GlobalTheory.PlaceDatum.isSBHalf_of_red e _ (frMapO S T βS βT) (GlobalTheory.PlaceDatum.frMapO_add βS βT)
      (GlobalTheory.PlaceDatum.exists_den_frMapO dS.1.fg dT.1.fg βS βT)
      ⟨K, hK, fun t ht => hC t (GlobalTheory.PlaceDatum.infPart_of_half hinf ht)⟩ P
      (fun y => omegaG L χ y * omegaQ Q L.r ξ 1 y) fun y y' h => by
        rw [GlobalTheory.PlaceDatum.omegaG_congr _ _ y y' fun PP hPP => h PP ((hP PP).2 (Or.inl hPP)),
          GlobalTheory.PlaceDatum.omegaQ_congr _ _ _ 1 y y' fun PP hPP => h PP ((hP PP).2 (Or.inr hPP))]
  obtain ⟨k1, k2⟩ := GlobalTheory.Chain.StepVac.placeModel_span_ne hv.1 dS dT (GlobalTheory.PlaceDatum.idemSum_mul_self he) he.2 hinf hTm hSB
  rw [← hall Tm hTm] at k1 k2
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 k1
  refine ⟨?_, k2 h0 fun hz => ?_, fun τ => ?_⟩
  · rw [← hc]
    exact GlobalTheory.FinTranslate.isTheta_sum_heisO_fin D ψ S T hv.1.1 f₀ hv.2.theta _ c.support (fun a => a.1) c fun a _ => a.2
  · obtain ⟨x, h1, h2, h3⟩ := exists_rect S T βS βT he
    have := congrFun hz x
    rw [if_pos ⟨h1, h2⟩] at this
    exact mul_ne_zero (omegaG_ne_zero hr L χ _ fun PP h => h3 PP ((hP PP).2 (Or.inl h)))
      (omegaQ_ne_zero L.hr (L.hr.trans hr) Q ξ 1 _ fun PP h => h3 PP ((hP PP).2 (Or.inr h))) this
  · rw [← hc]
    exact GlobalTheory.FockTranslate.isFockVacAt_sum D ψ θ S T hv.1.1 hv.2.inf f₀ hv.2.theta τ _ (hv.2.fock τ) _ c.support
      (fun a => a.1) c fun a _ => a.2

end GlobalTheory.InnerSteps

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasNormGroups
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne Neutral.B1

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocDict

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]

abbrev Kbar (w : HeightOneSpectrum (𝓞 E)) : Type := AlgebraicClosure (w.adicCompletion E)

abbrev GalLoc (w : HeightOneSpectrum (𝓞 E)) : Type := Kbar w ≃ₐ[w.adicCompletion E] Kbar w

def IsLocEmb (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (ι : Ω →ₐ[E] Kbar w) : Prop :=
  ∀ z, z ∈ A ↔ IsIntegral (w.adicCompletionIntegers E) (ι z)

def Lifts {w : HeightOneSpectrum (𝓞 E)} (ι : Ω →ₐ[E] Kbar w) (g : GalLoc w) (σ : G E Ω) : Prop :=
  ∀ z, g (ι z) = ι (σ z)

theorem Lifts.mul {w : HeightOneSpectrum (𝓞 E)} {ι : Ω →ₐ[E] Kbar w} {g g' : GalLoc w} {σ σ' : G E Ω}
    (H : Lifts ι g σ) (H' : Lifts ι g' σ') : Lifts ι (g * g') (σ * σ') := fun z => by
  rw [AlgEquiv.mul_apply, H', H]; rfl

theorem Lifts.eq {w : HeightOneSpectrum (𝓞 E)} {ι : Ω →ₐ[E] Kbar w} {g : GalLoc w} {σ σ' : G E Ω}
    (H : Lifts ι g σ) (H' : Lifts ι g σ') : σ = σ' :=
  AlgEquiv.ext fun z => ι.toRingHom.injective ((H z).symm.trans (H' z))

variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}

def HasNormGroups (h : IsPlaceOver A w) (ι : Ω →ₐ[E] Kbar w) (a : Weil h →* (w.adicCompletion E)ˣ) : Prop :=
  ∀ L : IntermediateField (w.adicCompletion E) (Kbar w), IsFiniteAbelian (w.adicCompletion E) L →
    ∀ (σ : Weil h) (g : GalLoc w), Lifts ι g σ → ((∀ z ∈ L, g z = z) ↔ a σ ∈ normGroup (w.adicCompletion E) L)

end GlobalTheory.LocDict

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianClassConditionOfChartClasses
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.HermTransport

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

open scoped TensorProduct

theorem reGL_refl_apply' {n : ℕ} (R : Type) [CommRing R] (g : GL (Fin n) R) : reGL rfl R g = g := by
  ext a b
  simp [reGL]

theorem reGL_refl_hom' {n : ℕ} (R : Type) [CommRing R] :
    (reGL (rfl : n = n) R).toMonoidHom = MonoidHom.id _ := by
  ext1 g
  exact reGL_refl_apply' R g

omit [StarRing E] in
theorem reL_refl' {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) : reL rfl L = L := by
  ext x
  simp [reL, reV]

theorem classTie_of_reindex (hc : CMData F E) (S : HSpace E) {n : ℕ} (h : S.rank = n) {σ : E →ₐ[F] E}
    (hσ : σ = hc.sig) {J : Matrix (Fin n) (Fin n) E}
    (hJ : ∀ a b, J a b = S.gram (Fin.cast h.symm a) (Fin.cast h.symm b))
    {U' : Subgroup (GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))} {Lb' : Submodule (𝓞 E) (Fin n → E)}
    {cl cl' : Type} (e : cl' ≃ cl) {stab : cl → Type} [∀ c, Group (stab c)] (lat : cl → Submodule (𝓞 E) S.V)
    (y : cl → UPts σ J (Formalism.L2.Herm.Af F))
    (y_bij : Function.Bijective (fun c => (Quotient.mk'' (y c) :
      ClassSet ((ratPts σ J (Formalism.L2.Herm.Af F)).subgroupOf (UPts σ J (Formalism.L2.Herm.Af F)))
        (U'.subgroupOf (UPts σ J (Formalism.L2.Herm.Af F))))))
    (y_lat : ∀ c (x : Fin n → E ⊗[F] Formalism.L2.Herm.Af F),
      x ∈ Formalism.L2.Herm.hatL (F := F) (reL h (Formalism.L2.Herm.crdLat S (lat c))) ↔
        ((y c).1⁻¹).1 *ᵥ x ∈ Formalism.L2.Herm.hatL (F := F) Lb')
    (stabI : ∀ c, stab c →* UJ (σ : E →+* E) J)
    (stabI_inj : ∀ c, Function.Injective (stabI c))
    (stabI_range : ∀ c (γ : UJ (σ : E →+* E) J), γ ∈ (stabI c).range ↔
      bc (inclE (F := F) (Formalism.L2.Herm.Af F)) γ.1 ∈ U'.map (MulAut.conj (y c).1).toMonoidHom)
    (Lb : Submodule (𝓞 E) (Fin S.rank → E)) (U : Subgroup (GL (Fin S.rank) (E ⊗[F] Formalism.L2.Herm.Af F)))
    (hLb : Lb' = reL h Lb) (hU : U' = U.map (reGL h _).toMonoidHom) :
    ∃ C : Formalism.L2.Herm.ClassTie hc S Lb U (fun c' => stab (e c')) (fun c' => lat (e c')),
      (∀ c', (y (e c')).1 = reGL h _ (C.y c').1) ∧ ∀ c' s, (stabI (e c') s).1 = reGL h _ (C.stabI c' s).1 := by
  subst h
  subst hσ
  obtain rfl : J = S.gram := by
    ext a b
    simpa using hJ a b
  subst hLb
  subst hU
  have hU0 : U.map (reGL (rfl : S.rank = S.rank) (E ⊗[F] Formalism.L2.Herm.Af F)).toMonoidHom = U := by
    rw [reGL_refl_hom', Subgroup.map_id]
  rw [hU0] at y_bij stabI_range
  simp only [reL_refl'] at y_lat
  refine ⟨⟨fun c' => y (e c'), y_bij.comp e.bijective, fun c' x => y_lat (e c') x, fun c' => stabI (e c'),
    fun c' => stabI_inj (e c'), fun c' γ => stabI_range (e c') γ⟩,
    fun c' => (reGL_refl_apply' _ _).symm, fun c' s => (reGL_refl_apply' _ _).symm⟩

end Gen

theorem latCrd_eq_reL (D : D7) (i : ℕ) (hi : i ≤ D.R.m) (L : Submodule (𝓞 D.host.E) (D.sp.X i).V) :
    latCrd D i hi L = reL (rankN D i hi) (Formalism.L2.Herm.crdLat (D.sp.X i) L) := by
  ext x
  simp [latCrd, reL, Formalism.L2.Herm.crdLat, reV, Formalism.L2.Herm.crd]

theorem classTie_of_chart : ∀ (D : D7) (i : ℕ) (hi : i ≤ D.R.m) {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} {cl cl' : Type} (e : cl' ≃ cl)
  {stab : cl → Type} [∀ c, Group (stab c)] (lat : cl → Submodule (𝓞 D.host.E) (D.sp.X i).V)
  (K : LevelChart D T bad i hi stab (fun c => latCrd D i hi (lat c)))
  {T' f' : ℕ} (L : Formalism.L2.Herm.StepLevel D.sp.cm (D.sp.X i) D.host.g T' f'),
  K.lev.Lb = reL (rankN D i hi) L.Lb → K.lev.U = L.U.map (reGL (rankN D i hi) _).toMonoidHom →
  ∃ C : Formalism.L2.Herm.ClassTie D.sp.cm (D.sp.X i) L.Lb L.U (fun c' => stab (e c')) (fun c' => lat (e c')),
    (∀ c', (K.y (e c')).1 = reGL (rankN D i hi) _ (C.y c').1) ∧
    ∀ c' s, (K.stabI (e c') s).1 = reGL (rankN D i hi) _ (C.stabI c' s).1 := by
  intro D i hi T bad cl cl' e stab _ lat K T' f' L hLb hU
  exact classTie_of_reindex D.sp.cm (D.sp.X i) (rankN D i hi) rfl (fun a b => rfl) e lat K.y K.y_bij
    (fun c x => by rw [← latCrd_eq_reL]; exact K.y_lat c x) K.stabI K.stabI_inj K.stabI_range L.Lb L.U hLb hU

end GlobalTheory.HermTransport
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HilbertInnerRowFormsEqLevelClassSum
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.TopGram

set_option maxHeartbeats 4000000 in

theorem topGram : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.BaseW F → ∀ (b : Bool) (t : T) (x y : Fin (rDim D A (F.lvl b).P (F.lvl b).ψ t) → D.what₂.LL), (((RealDat.nP F b)⁻¹ : ℝ) : ℂ) * ⟪R.jX t (rowForm A (F.lvl b).P (F.lvl b).ψ t x), R.jX t (rowForm A (F.lvl b).P (F.lvl b).ψ t y)⟫_ℂ = D.what₂.embLL (Formalism.DivisionValues.hform (rH D A (F.lvl b).P (F.lvl b).ψ t) x y) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hW b t x y
  have hHX := (hW.models.HX t).2.2
  have hjX := hW.models.jX t
  rw [hHX, hjX, hjX]
  have hiso := (GlobalTheory.classPres_extMem_extBij_isom _ _ _ _ _ _ _ _ _ _ (R.B.R t).pres).2.2
  have key : ∀ f f' : A.fam.amb.FR t, Bridge.adInner (Bridge.ratF D.sp.X') (levEnv D.sp.X' R.βX (R.datXt t)).J
      (R.B.R t).pres.y (R.B.jR t f) (R.B.jR t f') = D.what₂.embLL ((A.fam.R t).S.csum f f') := fun f f' => hiso f f'
  have hr : ∀ z, rowForm A (F.lvl b).P (F.lvl b).ψ t z =
      GlobalTheory.Mem.LiftForms.lvlForm (A.fam.R t).S (A.fam.R t).r (A.fam.lvl (F.lvl b).P (F.lvl b).ψ).P
        (A.fam.lvl (F.lvl b).P (F.lvl b).ψ).ψ z := fun z => rfl
  refine (congrArg (fun z => (((RealDat.nP F b)⁻¹ : ℝ) : ℂ) * z) (key (rowForm A (F.lvl b).P (F.lvl b).ψ t x) (rowForm A (F.lvl b).P (F.lvl b).ψ t y))).trans ?_
  rw [hr, hr, GlobalTheory.Mem.LiftForms.csum_lvlForm]
  have hc : (Nat.card ↥(A.fam.lvl (F.lvl b).P (F.lvl b).ψ).P : ℂ) ≠ 0 := by exact_mod_cast (Nat.card_pos).ne'
  have hn : (((RealDat.nP F b)⁻¹ : ℝ) : ℂ) = ((Nat.card ↥(A.fam.lvl (F.lvl b).P (F.lvl b).ψ).P : ℂ))⁻¹ := by
    rw [Complex.ofReal_inv]
    rfl
  rw [map_mul, map_natCast, hn, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  rfl

end GlobalTheory.Mem.TopGram
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionStarStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSmoothAutomorphicFunction_star : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D) (φ : GA D V → ℂ), IsAutFunSm θ V φ → IsAutFunSm θ V (fun g => star (φ g)) := by
  first | exact @GlobalTheory.Mem.AutConj.isAutFunSm_star | exact GlobalTheory.Mem.AutConj.isAutFunSm_star | (intros; apply GlobalTheory.Mem.AutConj.isAutFunSm_star <;> assumption)
end

