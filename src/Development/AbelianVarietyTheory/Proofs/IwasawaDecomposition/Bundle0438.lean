import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLtOfMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0132
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsMoveRight
import Formalism.LocalToGlobal.Columns.Bundle0016
import Formalism.LocalToGlobal.Columns.RecLevelCls
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RationalRootsDef
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FamilyClassSevenDutiesAndStableLattices
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsColumnInputAssembled
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsBaseJointFld
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0388
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0394
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0387
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0418
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0433
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0105
import Formalism.LocalToGlobal.GroupLattices.Joint0
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.Bundle0005
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameHeckeCharLocalEqInvTypeCharacter
import Formalism.LocalToGlobal.Columns.Bundle0040
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
import Formalism.LocalToGlobal.Columns.Bundle0017

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPtOfIffUnitaryDecoration
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Mem.Col2.PtDeco

theorem isPtOf_iff_decoRaw : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (g : GL (Fin n) (AfE F E)) (p : DecoF E n ST SG Q), Q = ∅ → (IsPtOf hc g p ↔ g ∈ UAd hc n ∧ p.deco.1 = decoRaw ST SG g) := by
  intro F E _ _ _ _ _ _ hc n _ ST SG Q g p hQ
  subst hQ
  have hlast : ∀ i : Fin n, i.1 + 1 = n → lastIdx n = i := fun i hi => Fin.ext (by simp [lastIdx]; omega)
  constructor
  · intro h
    have hg : g ∈ UAd hc n := h.uni
    have hN : p.deco.1.N = Formalism.UG.CS.globLat g (stdLat E n) := by
      have h1 := Formalism.UG.P.global_lattice_one_holds F E (Fin n) p.deco.1.N (Module.Finite.iff_fg.2 p.deco.2.lat.fg)
        p.deco.2.lat.span_eq_top
      ext v
      conv_lhs => rw [← h1]
      have e1 : ∀ (x : GL (Fin n) (AfE F E)) (Λ : Submodule (𝓞 E) (Fin n → E)) (v : Fin n → E),
          v ∈ Formalism.UG.CS.globLat x Λ ↔ ((x⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ
            (fun i => Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (v i)) ∈ Formalism.L2.Herm.hatL (F := F) Λ :=
        fun _ _ _ => Iff.rfl
      rw [e1, e1, inv_one, Units.val_one, Matrix.one_mulVec]
      exact h.lat _
    refine ⟨hg, Deco.Ok.ext_on p.deco.2 (decorated_lattice_exists hc n ST SG g hg) hN (fun P x hx => ?_) (fun w x hx => ?_)⟩
    · have hx' : x ∈ Formalism.UG.CS.globLat g (stdLat E n) := hN ▸ hx
      refine HasRes.unique (h.f P x hx (lastIdx n) (by simp [lastIdx]; have := NeZero.pos n; omega)) ?_
      simp only [decoRaw]
      rw [if_pos (le_locP _ _ hx')]
      exact PtExist.hasRes_redA _ ((mem_globLat g x).1 hx' _)
    · have hx' : x ∈ Formalism.UG.CS.globLat g (stdLat E n) := hN ▸ hx
      funext i
      refine HasRes.unique (h.be w x hx i) ?_
      simp only [decoRaw]
      rw [if_pos (le_locP _ _ hx')]
      exact PtExist.hasRes_redA _ ((mem_globLat g x).1 hx' i)
  · rintro ⟨hg, hd⟩
    have hN : p.deco.1.N = Formalism.UG.CS.globLat g (stdLat E n) := by rw [hd]; rfl
    refine ⟨hg, hN ▸ PtExist.carries_globLat g, fun P x hx i hi => ?_, fun w x hx i => ?_,
      fun P => absurd P.2 (Finset.notMem_empty _)⟩
    · rw [hN] at hx
      rw [hd]
      simp only [decoRaw]
      rw [if_pos (le_locP _ _ hx), hlast i hi]
      exact PtExist.hasRes_redA _ ((mem_globLat g x).1 hx i)
    · rw [hN] at hx
      rw [hd]
      simp only [decoRaw]
      rw [if_pos (le_locP _ _ hx)]
      exact PtExist.hasRes_redA _ ((mem_globLat g x).1 hx i)

end GlobalTheory.Mem.Col2.PtDeco

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KsCondExact
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Fld GlobalTheory.Mem.HD NumberField IsDedekindDomain
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.KsExactCond

theorem ksCond_exact : RayField → PrincipalIdealSt → CMCurveGoodOutsidePrimeSt →
    V4.KsCond fun B f => ∃ δ : FieldDat B.toPre, B.KsExact δ f := by
  intro hR hP hA
  refine ⟨Col2.InEx.ev_of_forall fun K B₀ f₀ S₁ S₂ hO s1 s2 => ?_, fun B B' f f' e hf hS => ?_⟩
  · obtain ⟨δ⟩ := nonempty_fieldDat hR hA B₀.toPre
    obtain ⟨B₁, e₁, k⟩ := (GlobalTheory.Mem.KsBase.exists_base_listField hR hP _ f₀ δ).2
    obtain ⟨B₂, e₂, k₂, l₂⟩ := Inh.exists_fixed B₁ (S₁ B₁.KsC) (s1 _)
    obtain ⟨B, e, l₃⟩ := BaseEnl.exists_enl B₂ (S₂ B₁.KsC B₂.fixedCoefficientFieldInComplex) (s2 _ _)
    have hk : B.KsC = B₁.KsC := e.KsC_eq.trans k₂
    have e' : B.toPre = B₀.toPre := e.1.trans (e₂.trans e₁)
    have hH : Has₂ B (S₁ B.KsC) (S₂ B.KsC B.fixedCoefficientFieldInComplex) := by
      rw [hk, Has₂, e.fixedCoefficientField_eq]
      exact ⟨l₂, l₃⟩
    rw [← hk] at k
    clear e e₁ e₂ hO
    generalize B₀.toPre = P₀ at *
    subst e'
    exact ⟨B, f₀, rfl, HEq.rfl, ⟨δ, k⟩, hH⟩
  · have e' := e.1
    unfold Base.KsExact at hS ⊢
    rw [e.KsC_eq]
    clear e
    generalize B.KsC = F at *
    generalize B.toPre = P at *
    subst e'
    obtain rfl := eq_of_heq hf
    exact hS

end GlobalTheory.Mem.KsExactCond
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemRangeOfPowG
section
noncomputable section

namespace GlobalTheory.Mem.Top.ColOwe

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem natCast_kv_eq_zero (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (p : ℕ) (h : (p : 𝓞 F) ∈ v.asIdeal) : (p : kv F v) = 0 := by

  have hval : Valued.v ((algebraMap (𝓞 F) (v.adicCompletionIntegers F) (p : 𝓞 F) :
      v.adicCompletion F)) < 1 := by
    rw [HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact (v.valuation_lt_one_iff_mem (K := F) _).2 h
  have hmax : algebraMap (𝓞 F) (v.adicCompletionIntegers F) (p : 𝓞 F) ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) :=
    (Valuation.mem_maximalIdeal_iff _ Valued.v).2 hval
  have hres := (IsLocalRing.residue_eq_zero_iff _).2 hmax
  simpa using hres

theorem mem_range_of_pow_g (B : Base) (i : Fin 2) (z : ℂ) (hz : z ^ B.host.g i = 1) : ∃ r : B.LL, B.embLL r = z := by
  have hp : (B.host.g i).Prime := B.host.g_prime i

  have hmem : B.host.g i * (B.host.g i - 1) ∈ [B.toPre.restRowsFiniteGroupCard, B.host.g 0 * (B.host.g 0 - 1),
      B.host.g 1 * (B.host.g 1 - 1), 3 ^ 4, 5 ^ 4] := by
    fin_cases i <;> simp
  obtain ⟨z0, -, hz0⟩ := B.roots_Ks _ hmem
  have hN : B.host.g i * (B.host.g i - 1) ≠ 0 :=
    Nat.mul_ne_zero hp.ne_zero (by have := hp.two_le; omega)
  have hprim : IsPrimitiveRoot (B.embLL z0) (B.host.g i * (B.host.g i - 1)) := by
    rw [hz0]; exact Complex.isPrimitiveRoot_exp _ hN

  have hprim' : IsPrimitiveRoot (B.embLL z0 ^ (B.host.g i - 1)) (B.host.g i) :=
    hprim.pow (Nat.pos_of_ne_zero hN) (mul_comm _ _)
  have : NeZero (B.host.g i) := ⟨hp.ne_zero⟩
  obtain ⟨k, -, hk⟩ := hprim'.eq_pow_of_pow_eq_one hz
  exact ⟨(z0 ^ (B.host.g i - 1)) ^ k, by rw [map_pow, map_pow, hk]⟩

theorem psi0Rat (X : Stages) (T : ∀ u, Forms0 X.toD7 u) (u : X.toD7.what₂.Word) : Formalism.L2.G.LevelZeroCharacterRational T u := by
  intro i v h x

  have hx : ((T u).gl.psi0 i v h x) ^ X.toD7.host.g i = 1 := by
    rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, natCast_kv_eq_zero _ v _ h, zero_mul,
      AddChar.map_zero_eq_one]
  exact mem_range_of_pow_g X.B i _ hx

variable {D : D7}

def levOf (C : ColsTiedSym D) : LevelData D := C.herm.base.lev0

def formsOf (C : ColsTiedSym D) (u : D.what₂.Word) : Forms0 D u := (C.forms u).to0

def errOf (H : Formalism.L2.Herm.ColsHermS D) : ErrX D := (GlobalTheory.Mem.ErrTies.exists_errX D H).choose

theorem errOf_piG (H : Formalism.L2.Herm.ColsHermS D) : (errOf H).piG = (H.levelZeroCompatibility D.u₀).piG :=
  (GlobalTheory.Mem.ErrTies.exists_errX D H).choose_spec.1

theorem errOf_piT (H : Formalism.L2.Herm.ColsHermS D) (u : D.what₂.Word) : (errOf H).piT u = (H.atT u).piU :=
  (GlobalTheory.Mem.ErrTies.exists_errX D H).choose_spec.2.1 u

theorem errOf_vPl (H : Formalism.L2.Herm.ColsHermS D) (u : D.what₂.Word) (v : (D.mem u).A.vT) :
    (errOf H).vPl u v = (H.base.vT u v).1 :=
  (GlobalTheory.Mem.ErrTies.exists_errX D H).choose_spec.2.2.1 u v

theorem joint0 (C : ColsTiedSym D) (u : D.what₂.Word) : Joint0 (levOf C) u (formsOf C u) := by
  unfold levOf formsOf
  exact C.joint0 u

theorem dGamChoice_of_lcm (X : Stages) (hDG : ∀ u μ, (X.C.chTw u μ).DGam = GlobalTheory.Mem.Col2.DGam X.B.fields.E X.B.R) :
    DGamChoice_at X.toD7 := by
  intro M hM u

  have hc : (X.toD7.mem u).C = X.C.chTw u X.C.mu0 := (X.C.memberColumns_twistedChain_base u).symm
  rw [hc, hDG u X.C.mu0]
  have hf : X.B.fields.f = X.B.R.f := (GlobalTheory.Mem.FieldsLaws.fields_satisfy_definite_laws X.B).2
  refine GlobalTheory.Mem.Col2.DGam_dvd_of_minkMult X.B.R (GlobalTheory.Mem.FieldsLaws.fields_ok (B := X.B)) M ?_
  rw [hf]
  exact hM

theorem colLay_of_herm (X : Stages) (hX : Nonempty (PreX X.B.toPre))
    (hDG : ∀ u μ, (X.C.chTw u μ).DGam = GlobalTheory.Mem.Col2.DGam X.B.fields.E X.B.R)
    (H : Formalism.L2.Herm.ColsHermS X.toD7) (T : ∀ u, Forms0 X.toD7 u) (hJ : ∀ u, Joint0 H.base.lev0 u (T u)) :
    ColLay X.toD7 H.base.lev0 (errOf H) where
  piG_lev := (GlobalTheory.Mem.ErrTies.exists_errX X.toD7 H).choose_spec.2.2.2.1
  piT_lev := (GlobalTheory.Mem.ErrTies.exists_errX X.toD7 H).choose_spec.2.2.2.2.1
  seen := (GlobalTheory.Mem.ErrTies.exists_errX X.toD7 H).choose_spec.2.2.2.2.2.1
  tauOf := (GlobalTheory.Mem.ErrTies.exists_errX X.toD7 H).choose_spec.2.2.2.2.2.2
  one u μ := by
    have h0 : (X.C.chTw X.B.u₀ X.C.mu0).DGam = (X.C.mem X.B.u₀).C.DGam :=
      congrArg (fun c => c.DGam) (X.C.memberColumns_twistedChain_base X.B.u₀)
    exact (hDG u μ).trans ((hDG X.B.u₀ X.C.mu0).symm.trans h0)
  mink := dGamChoice_of_lcm X hDG
  atT := GlobalTheory.T.heckeUOperator_rational_invertible_ramifiedForms X hX H T hJ (fun u => psi0Rat X T u)

theorem colLay_of_tied (X : Stages) (hX : Nonempty (PreX X.B.toPre))
    (hDG : ∀ u μ, (X.C.chTw u μ).DGam = GlobalTheory.Mem.Col2.DGam X.B.fields.E X.B.R) (C : ColsTiedSym X.toD7) :
    ColLay X.toD7 (levOf C) (errOf C.herm) :=
  colLay_of_herm X hX hDG C.herm (formsOf C) (joint0 C)

end GlobalTheory.Mem.Top.ColOwe

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MoveDownLevelPrimeKeepsChart
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2

section Same

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}

structure SameG {y : Ys X n} (p p' : PtY ST SG Q y) : Prop where
  fr : p'.1.1.1.2 = p.1.1.1.2
  ys : p'.1.2 = p.1.2
  at_eq : ∀ w : SG, p'.1.1.deco.1.at w.1 = p.1.1.deco.1.at w.1
  be : p'.1.1.deco.1.be = p.1.1.deco.1.be

theorem SameG.refl {y : Ys X n} (p : PtY ST SG Q y) : SameG p p :=
  ⟨rfl, rfl, fun _ => rfl, rfl⟩

private theorem locP_gmap_eq_of_locP_eq {E : Type} [Field E] [NumberField E] {n : ℕ} (P : HeightOneSpectrum (𝓞 E))
    (g : Sp E n ≃ₗ[E] Sp E n) {N N' : Submodule (𝓞 E) (Sp E n)}
    (h : Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N' = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N) :
    Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Formalism.HermitianLatticesTheory.gmap g N') = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Formalism.HermitianLatticesTheory.gmap g N) := by
  have hs : ∀ (s : 𝓞 E) (z : Sp E n), g.symm (s • z) = s • g.symm z := fun s z =>
    ((g.symm : Sp E n →ₗ[E] Sp E n).restrictScalars (𝓞 E)).map_smul s z
  have hmemL : ∀ (M : Submodule (𝓞 E) (Sp E n)) (x : Sp E n),
      x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal M ↔ ∃ s ∈ P.asIdeal.primeCompl, s • x ∈ M := fun _ _ => Iff.rfl

  have hmemg : ∀ (M : Submodule (𝓞 E) (Sp E n)) (x : Sp E n),
      x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Formalism.HermitianLatticesTheory.gmap g M) ↔ g.symm x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal M := by
    intro M x
    rw [hmemL, hmemL]
    constructor
    · rintro ⟨s, hs0, hx⟩
      obtain ⟨z, hz, hzx⟩ := Submodule.mem_map.mp hx
      have hz' : z = g.symm (s • x) := by
        rw [← hzx]
        simp
      exact ⟨s, hs0, by rw [← hs, ← hz']; exact hz⟩
    · rintro ⟨s, hs0, hx⟩
      refine ⟨s, hs0, Submodule.mem_map.mpr ⟨g.symm (s • x), by rw [hs]; exact hx, by simp⟩⟩
  ext x
  rw [hmemg, hmemg, h]

theorem SameG.smul {y : Ys X n} {Λ : LevFam X.E X.K n SG} {Θ : LevQFam X.E X.K n Q} (h : FrmG Λ Θ) {p p' : PtY ST SG Q y}
    (r : SameG p p') : SameG ((ptYAct y Λ Θ).toSMul.smul h p) ((ptYAct y Λ Θ).toSMul.smul h p') where
  fr := congrArg (fun F => fun P => (FrmG.incl Λ Θ h).1.1 * F P * ((FrmG.incl Λ Θ h).2.2 P)⁻¹.1) r.fr
  ys := congrArg (fun S => (fun v => h.1.1 v) '' S) r.ys
  at_eq w := by
    show Formalism.HermitianLatticesTheory.localization₂ w.1.asIdeal (Formalism.HermitianLatticesTheory.gmap h.1.1 p'.1.1.deco.1.N) =
      Formalism.HermitianLatticesTheory.localization₂ w.1.asIdeal (Formalism.HermitianLatticesTheory.gmap h.1.1 p.1.1.deco.1.N)
    exact locP_gmap_eq_of_locP_eq w.1 h.1.1 (r.at_eq w)
  be := congrArg (fun B => fun w x => ((FrmG.incl Λ Θ h).2.1 w).1.mulVec (B w (h.1.1.symm x))) r.be

theorem SameG.dn {y : Ys X n} (p : PtY ST SG Q y) (P : ST) (hP : MoveHyp ST SG P) (f' : Sp X.E n → 𝓞 X.E ⧸ P.1.asIdeal) :
    SameG p (p.mv (p.1.1.deco.dn P f')) := by
  classical
  unfold PtY.mv
  refine Eq.mpr (apply_dite (SameG p) _ _ _) ?_
  split
  · refine ⟨rfl, rfl, fun w => ?_, ?_⟩
    · show (p.1.1.deco.dn P f').1.at w.1 = p.1.1.deco.1.at w.1
      unfold DecoSet.dn
      split_ifs with hok
      · exact ((p.1.1.deco.2.dnN_spec P hP.ne).2.2.1 w.1 (hP.sg w).1 (hP.sg w).2).localization_eq
      · rfl
    · show (p.1.1.deco.dn P f').1.be = p.1.1.deco.1.be
      unfold DecoSet.dn
      split_ifs <;> rfl
  · exact SameG.refl p

end Same

section Coset

private theorem cosetIn_eq_of_sameG' {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)}
    {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}
    {q q' : PtAt R sel mu cst u j} (r : SameG q q') : cosetIn q' = cosetIn q := by
  have hfr : ∀ P, frsF sel mu q'.1.1 P = frsF sel mu q.1.1 P := by
    intro P
    unfold frsF
    split_ifs with hP
    · unfold Deco.liftFr
      rw [r.at_eq ⟨P.1, hP⟩, r.be]
    · exact congrFun r.fr _
  funext P
  unfold cosetIn
  rw [r.ys, hfr P]

open Classical GlobalTheory.TopStep in

theorem cosetIn_eq_of_sameG {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)}
    {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ} (hX : X.Ok) (hPr : Pr.Ok)
    {q q' : PtAt R sel mu cst u j} (r : SameG q q') : cosetIn q' = cosetIn q :=
  cosetIn_eq_of_sameG' r

end Coset

section Normal

theorem prefRep_pref {G D : Type} [Group G] [MulAction G D] (pref : D → Prop) (q : MulAction.orbitRel.Quotient G D)
    (h : ∃ p, Quotient.mk (MulAction.orbitRel G D) p = q ∧ pref p) : pref (prefRep pref q) := by
  unfold prefRep
  rw [dif_pos h]
  exact h.choose_spec.2

theorem GStep.NormalFor.eq {E K A : Type} [Field E] [NumberField E] [Field K] {n : ℕ} {S : GStep E K n} {b : S.β} {f : S.D b → A}
    {q q' : S.D b} (hq : S.NormalFor b f q) (hq' : S.NormalFor b f q')
    (h : ∀ r, (∃ g : S.G b, r = f (g • q)) ↔ ∃ g : S.G b, r = f (g • q')) : f q = f q' := by
  unfold GStep.NormalFor at hq hq'
  rw [hq, hq']
  exact congrArg (@Classical.epsilon A ⟨f q⟩) (funext fun r => propext (h r))

theorem GStep.exists_normalFor {E K A : Type} [Field E] [NumberField E] [Field K] {n : ℕ} (S : GStep E K n) (b : S.β) (f : S.D b → A)
    (q : S.D b) : ∃ g : S.G b, S.NormalFor b f (g • q) := by
  have hex : ∃ r, ∃ g : S.G b, r = f (g • q) := ⟨f q, 1, by rw [one_smul]⟩
  obtain ⟨g, hg⟩ := Classical.epsilon_spec hex
  refine ⟨g, ?_⟩
  have hset : (fun r => ∃ g : S.G b, r = f (g • q)) = (fun r => ∃ g' : S.G b, r = f (g' • g • q)) := by
    funext r
    apply propext
    constructor
    · rintro ⟨g', rfl⟩
      exact ⟨g' * g⁻¹, by rw [mul_smul, inv_smul_smul]⟩
    · rintro ⟨g', rfl⟩
      exact ⟨g' * g, by rw [mul_smul]⟩
  unfold GStep.NormalFor
  exact hg.symm.trans (congrArg (@Classical.epsilon A ⟨f q⟩) hset)

theorem GStep.prefRep_eq_of_normal {E K A : Type} [Field E] [NumberField E] [Field K] {n : ℕ} (S : GStep E K n) (b : S.β) (f : S.D b → A)
    (pf : S.D b → Prop) (hn : ∀ q : MulAction.orbitRel.Quotient (S.G b) (S.D b), S.NormalFor b f (prefRep pf q)) (q : MulAction.orbitRel.Quotient (S.G b) (S.D b)) (d' : S.D b)
    (hd : ∀ h : S.G b, f (h • d') = f (h • prefRep pf q)) :
    f (prefRep pf (Quotient.mk (MulAction.orbitRel (S.G b) (S.D b)) d')) = f (prefRep pf q) := by
  obtain ⟨k, hk⟩ : ∃ k : S.G b, k • d' = prefRep pf (Quotient.mk (MulAction.orbitRel (S.G b) (S.D b)) d') :=
    Quotient.exact (prefRep_spec pf (Quotient.mk (MulAction.orbitRel (S.G b) (S.D b)) d'))
  refine GStep.NormalFor.eq (hn _) (hn q) fun r => ⟨?_, ?_⟩
  · rintro ⟨g, rfl⟩
    exact ⟨g * k, by rw [← hk, ← mul_smul, hd]⟩
  · rintro ⟨g, rfl⟩
    exact ⟨g * k⁻¹, by rw [← hd, ← hk, mul_smul, inv_smul_smul]⟩

theorem GStep.prefRep_normal {E K A : Type} [Field E] [NumberField E] [Field K] {n : ℕ} (S : GStep E K n) (b : S.β) (f : S.D b → A)
    (pf : S.D b → Prop) (hpf : ∀ p, pf p → S.NormalFor b f p) (hnp : ∀ p, S.NormalFor b f p → pf p)
    (q : MulAction.orbitRel.Quotient (S.G b) (S.D b)) : S.NormalFor b f (prefRep pf q) := by
  obtain ⟨g, hg⟩ := GStep.exists_normalFor S b f (Quotient.out q)
  have hex : ∃ p, Quotient.mk (MulAction.orbitRel (S.G b) (S.D b)) p = q ∧ pf p :=
    ⟨g • Quotient.out q, (Quotient.sound (s := MulAction.orbitRel (S.G b) (S.D b)) (MulAction.mem_orbit _ g)).trans
      (Quotient.out_eq q), hnp _ hg⟩
  exact hpf _ (prefRep_pref pf q hex)

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

theorem TC.pref_of_normalFor (u : B.Word) (a : I.ι) (j : ℕ) (hj : j + 1 = B.R.m) (b : (I.stp0 u a j).β) (p : (I.stp0 u a j).D b)
    (h : (I.stp0 u a j).NormalFor b (fun q' : (I.stp0 u a j).D b => cosetIn q') p) : I.pref u a j b p := by
  have hm := B.R.two_le_m
  refine ⟨fun h0 => absurd hj (by omega), fun _ => h, ?_⟩
  show ∀ h : j = B.R.m, _
  intro hjm
  exact absurd hjm (by omega)

private theorem TC.cosetIn_rep_cl_dn_eq (hPr : (B.primes X).Ok) (u : B.Word) (a : I.ι) (i : ℕ) (v : (B.primes X).vT u)
    (c : (I.stp u a i).Cl) (f : Sp B.fields.E (B.R.N i) → Res v.1) :
    cosetIn ((I.stp u a i).rep ((I.stp u a i).cl c.1 (((I.atIn u a).A i).dn c.1 ((I.stp u a i).rep c) v f))) =
      cosetIn ((I.stp u a i).rep c) := by
  obtain ⟨b, q⟩ := c
  have r0 : SameG ((I.stp u a i).rep ⟨b, q⟩) (((I.atIn u a).A i).dn b ((I.stp u a i).rep ⟨b, q⟩) v f) :=
    SameG.dn _ v (moveHyp_of_ok hPr u v) f
  by_cases hi : i + 1 = B.R.m
  · exact GStep.prefRep_eq_of_normal (I.stp0 u a i) b (fun q' => cosetIn q') (I.pref u a i b)
      (GStep.prefRep_normal (I.stp0 u a i) b _ (I.pref u a i b) (fun p hp => hp.2.1 hi)
        (fun p hp => I.pref_of_normalFor u a i hi b p hp)) q _
      (fun h => cosetIn_eq_of_sameG' (SameG.smul h r0))
  ·
    have hemp : ∀ p : PtAt B.R I.sel (I.tup a) (I.cst a) u i, cosetIn p = fun _ => ∅ := by
      intro p
      have hys : ∀ (Y : Set (Sp B.fields.E (B.R.N i))) (N : Submodule (𝓞 B.fields.E) (Sp B.fields.E (B.R.N i))),
          Y ∈ (ysAt B.R I.sel (I.tup a) (I.cst a) i).ys N → Y = ∅ := by
        intro Y N hY
        unfold ysAt at hY
        rw [if_neg hi] at hY
        exact hY
      have hp : p.1.2 = ∅ := hys _ _ p.2
      funext P
      unfold cosetIn
      rw [hp]
      ext z
      simp
    exact (hemp _).trans (hemp _).symm

end Normal

theorem TC.dn_keeps_chart : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))) (eY : (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi) (eV : (I.atT l u a).vT ≃ {v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) // (B.T u : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal}) (L : LevelCompatibleLattices (D := (I.rec7 l Z)) (I.fm l u a) (B.T u) (I.resT l u a) i hi fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c)), I.ReadsK l Z u a i hi chOf K → I.IdY l Z u a i hi eY → I.IdV l u a eV → I.IdL l Z u a i hi L → ∀ (v : (I.atT l u a).vT) (β : Ch) (c : {c // chOf c = β}) (g : Module.Dual (Res v.1) (((I.atIn u a).A i).lk v c.1)), g ≠ 0 → chOf ((I.fm l u a).dn i v c.1 g) = β := by
  intro B X I _ _ l Z u a i hi bad Ch chOf K eY eV L hK _ _ _ v β c g _

  obtain ⟨k, hR⟩ := hK
  exact ((hR.key ((I.fm l u a).dn i v c.1 g) c.1).mpr ⟨rfl, I.cosetIn_rep_cl_dn_eq l.pr u a i v c.1 _⟩).trans c.2

end GlobalTheory.Mem.Col2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PlaceOverSplitPlaceEqChosenOrConjugate
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.PlaceOverSplit

theorem eq_or_eq_cP : ∀ (D : D7), D.host.F = maximalRealSubfield D.host.E → ∀ (s : SplitPlace D.host.E) (Q : Formalism.L2.DIV.Pl D.host.E), Q.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) = s.v.asIdeal → Q = s.w ∨ Q = GlobalTheory.IdemSupport.cP s.w := by
  intro D _ s Q hQ
  rcases GlobalTheory.SplitConjPlace.eq_or_eq_conjPlE s.w Q (hQ.trans s.w_under.symm) with e | e
  · exact Or.inl e
  · refine Or.inr (e.trans (HeightOneSpectrum.ext (Ideal.ext fun x => ?_)))
    rw [GlobalTheory.SplitConjPlace.mem_conjPlE, GlobalTheory.IdemSupport.mem_cP]
    have : IsCMField.ringOfIntegersComplexConj D.host.E x = GlobalTheory.IdemSupport.cO D x := by
      apply RingOfIntegers.ext
      rw [IsCMField.coe_ringOfIntegersComplexConj, GlobalTheory.IdemSupport.cO_coe]
      rfl
    rw [this]

end GlobalTheory.PlaceOverSplit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SetStab
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

namespace GlobalTheory.Mem.Col2.MemChart

def bar {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} {y : Ys X n} (q : PtY ST SG Q y) (w : SG) :
    Set (Fin n → 𝓞 X.E ⧸ w.1.asIdeal) :=
  {v | ∃ z ∈ q.1.2, v = q.1.1.deco.1.be w ((qOf w.1 : X.E) • z)}

def setStab {κ : Type} [CommRing κ] {n : ℕ} (C : Set (Fin n → κ)) : Subgroup (GL (Fin n) κ) where
  carrier := {h | ∀ v, h.1 *ᵥ v ∈ C ↔ v ∈ C}
  one_mem' v := by simp
  mul_mem' {a b} ha hb v := by
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, ha, hb]
  inv_mem' {a} ha v := by
    rw [← ha, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

end GlobalTheory.Mem.Col2.MemChart
end
end

