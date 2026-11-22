import Formalism.LocalToGlobal.Columns.Bundle0046
import Formalism.LocalToGlobal.Columns.Bundle0024
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.Bundle0003
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC
import Formalism.LocalToGlobal.Columns.Bundle0013
import Formalism.LocalToGlobal.Columns.Bundle0011
import Formalism.LocalToGlobal.Columns.Bundle0038
import Formalism.LocalToGlobal.Columns.Bundle0047
import Formalism.LocalToGlobal.Columns.RecLevelCls
import Formalism.LocalToGlobal.Columns.AdelicLemmas
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsSpan
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0011
import Formalism.LocalToGlobal.Columns.MemLocPOfSmul

-- bundled from Formalism.LocalToGlobal.Columns.ChainLawXi
section
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section Units

variable {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {K : Type} [Field K]

theorem clX_unitV_ne (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {a : E} (hU : IsUnit (redP P a)) : LocE.unitV χ a ≠ 0 := by
  unfold LocE.unitV
  rw [dif_pos hU]
  exact Units.ne_zero _

theorem clX_unitV_one (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) : LocE.unitV χ (1 : E) = 1 := by
  have h1 : redP P (1 : E) = 1 := by
    have := reduction_coe P (1 : 𝓞 E)
    simpa using this
  have hU : IsUnit (redP P (1 : E)) := by rw [h1]; exact isUnit_one
  unfold LocE.unitV
  rw [dif_pos hU]
  have : hU.unit = 1 := Units.ext (by simpa using h1)
  rw [this, map_one, Units.val_one]

theorem clX_unitV_inv (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {a : E} (hu : IntAt P a) (hu' : IntAt P a⁻¹) (h0 : a ≠ 0) :
    LocE.unitV χ a⁻¹ = (LocE.unitV χ a)⁻¹ := by
  have hne := clX_unitV_ne χ (isUnit_reduction_of_integralAt_inv hu hu' h0)
  have hm := unitV_mul_unit χ hu hu' h0 a⁻¹
  rw [inv_mul_cancel₀ h0, clX_unitV_one] at hm
  exact eq_inv_of_mul_eq_one_left hm.symm

end Units

section Assembly

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
  {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ}

end Assembly

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.DetChrChi
section
noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace Formalism.L2.Col

namespace DetChrChi

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs)

def ChiReads (D : D7) {σ₀ : X.K →+* ℂ} (K : KerAmbTied D X σ₀) (Dc : DetChr X R.m) (hc : CMData X.F X.E) (u : Pr.Word) : Prop :=
  ∀ j (cl : StCl W Λ u j), ∃ y : D.Dt,
    ((D.chiD y : ℂˣ) : ℂ) = σ₀ ((Formalism.L2.DIV.detTw hc.sig Dc.chi (repPt W Λ hc u j cl) : X.Kˣ) : X.K) ∧
      K.idl (QuotientGroup.mk y) = TaylorLogMetric.detId D (StandardLatticesGL3.stdL D (R.N j)) (K.seam.lat (repN W Λ u j cl))

theorem pt_of_reads (D : D7) {σ₀ : X.K →+* ℂ} (K : KerAmbTied D X σ₀) (Dc : DetChr X R.m) (hc : CMData X.F X.E) (u : Pr.Word)
    (h : ChiReads W Λ D K Dc hc u) (j : ℕ) (cl : StCl W Λ u j) :
    σ₀ ((Formalism.L2.DIV.detTw hc.sig Dc.chi (repPt W Λ hc u j cl) : X.Kˣ) : X.K) =
      K.χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D (R.N j)) (K.seam.lat (repN W Λ u j cl))) := by
  obtain ⟨y, h1, h2⟩ := h j cl
  rw [← h1, K.χ_rec, ← h2, TaylorLogMetric.chiRec_idl D K.idl K.idl_ok.1]
  rfl

theorem chiDetTie_of_reads (D : D7) {σ₀ : X.K →+* ℂ} (K : KerAmbTied D X σ₀) (Dc : DetChr X R.m) (hc : CMData X.F X.E) (u : Pr.Word)
    (h : ChiReads W Λ D K Dc hc u) : ChiDetTie W Λ σ₀ Dc hc K.amb u :=
  DetChrOf.chiDetTie_of_pt W Λ σ₀ Dc hc K.amb u (fun a N => K.χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D a) (K.seam.lat N)))
    (fun _ _ _ _ => rfl) (pt_of_reads W Λ D K Dc hc u h)

section Lat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}

theorem carries_globLat (g : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :
    Formalism.L2.Herm.Carries g (stdLat E n) (Formalism.UG.CS.globLat g (stdLat E n)) := fun x =>
  Formalism.UG.P.span_recovery_of_integral_adelic_approx Formalism.UG.P.csGlob_intAdApprox F E (Fin n) (stdLat E n)
    (Module.Finite.iff_fg.2 (stdLat_lattice (E := E) (n := n)).fg) (stdLat_lattice (E := E) (n := n)).span_eq_top g x

theorem isSDLat_globLat (hc : CMData F E) {x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (hx : x ∈ UAd hc n) :
    IsSDLat E n (Formalism.UG.CS.globLat x (stdLat E n)) := by
  have hlat := Formalism.UG.P.global_lattice_isLattice_holds F E (Fin n) (stdLat E n)
    (Module.Finite.iff_fg.2 (stdLat_lattice (E := E) (n := n)).fg) (stdLat_lattice (E := E) (n := n)).span_eq_top x
  have hU := globLat_unimodular hc n hx
  refine ⟨hlat.fg, hlat.span_eq_top, fun y => ?_⟩
  conv_lhs => rw [← hU]
  rw [mem_dual]
  refine forall₂_congr fun z _ => ?_
  rw [Submodule.mem_one, RingHom.mem_range]
  exact Iff.rfl

end Lat

section Rep

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs)

theorem repN_eq_globLat (hc : CMData X.F X.E) (u : Pr.Word) (j : ℕ) (hS : DecoPtSurj hc (R.N j) (Pr.vT u) Pr.vGs)
    (cl : StCl W Λ u j) :
    repN W Λ u j cl = Formalism.UG.CS.globLat (F := X.F) (repPt W Λ hc u j cl) (stdLat X.E (R.N j)) := by
  have : NeZero (R.N j) := ⟨(R.N_pos j).ne'⟩
  have h1 := decoOf_ptOf hc (R.N j) (Pr.vT u) Pr.vGs hS ((stepGSD W Λ u j).outSec.rep cl)
  have hok := decorated_lattice_exists hc (R.N j) (Pr.vT u) Pr.vGs _ (ptOf hc (R.N j) (Pr.vT u) Pr.vGs ((stepGSD W Λ u j).outSec.rep cl)).2
  show ((stepGSD W Λ u j).outSec.rep cl).1.N = _
  rw [← h1]
  unfold decoOf
  rw [dif_pos hok]
  rfl

theorem carries_rep (hc : CMData X.F X.E) (u : Pr.Word) (j : ℕ) (hS : DecoPtSurj hc (R.N j) (Pr.vT u) Pr.vGs)
    (cl : StCl W Λ u j) :
    Formalism.L2.Herm.Carries (repPt W Λ hc u j cl) (stdLat X.E (R.N j)) (repN W Λ u j cl) := by
  rw [repN_eq_globLat W Λ hc u j hS cl]
  exact carries_globLat (F := X.F) (E := X.E) _

end Rep

section Rel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs)

def RelReads (D : D7) {σ₀ : X.K →+* ℂ} (K : KerAmbTied D X σ₀) (Dc : DetChr X R.m) (hc : CMData X.F X.E) (u : Pr.Word) : Prop :=
  ∀ j (cl : StCl W Λ u j), ∃ y : D.Dt,
    ((D.chiD y : ℂˣ) : ℂ) = σ₀ ((Formalism.L2.DIV.detTw hc.sig Dc.chi (repPt W Λ hc u j cl) : X.Kˣ) : X.K) ∧
      ∃ L L' : SDLat D.host.E (R.N j), L.1 = StandardLatticesGL3.stdL D (R.N j) ∧ L'.1 = K.seam.lat (repN W Λ u j cl) ∧
        (QuotientGroup.mk y : D.Dt ⧸ D.UO) = D.relDet (R.N j) L L'

theorem chiReads_of_rel (D : D7) {σ₀ : X.K →+* ℂ} (K : KerAmbTied D X σ₀) (Dc : DetChr X R.m) (hc : CMData X.F X.E) (u : Pr.Word)
    (h : RelReads W Λ D K Dc hc u) : ChiReads W Λ D K Dc hc u := by
  intro j cl
  obtain ⟨y, h1, L, L', hL, hL', hy⟩ := h j cl
  refine ⟨y, h1, ?_⟩
  rw [hy, K.idl_ok.2.2.2.2 (R.N j) L L', hL, hL']

theorem chiDetTie_of_rel (D : D7) {σ₀ : X.K →+* ℂ} (K : KerAmbTied D X σ₀) (Dc : DetChr X R.m) (hc : CMData X.F X.E) (u : Pr.Word)
    (h : RelReads W Λ D K Dc hc u) : ChiDetTie W Λ σ₀ Dc hc K.amb u :=
  chiDetTie_of_reads W Λ D K Dc hc u (chiReads_of_rel W Λ D K Dc hc u h)

end Rel

end DetChrChi

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.TwQLat
section
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.L2.DIV (Pl kP underPl St)
open Formalism.UG Formalism.HermitianLatticesTheory

section QLat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable {hc : Formalism.BasicNotions.CMData F E} {n : ℕ} [NeZero n] {ST SG Q : Finset (Pl E)} {K : Type} [Field K] {Θ : LevQFam E K n Q}

theorem qdf_frExists : FrExists (n := n) ST SG Q := fun d P => DetChrL.frame_exists P.1 d.2.lat

abbrev qPi (q : QLoc hc n Q Θ) (P : Q) : E ⊗[F] Formalism.L2.Herm.Af F →+* (qv F P.1).adicCompletion F :=
  ((RingHom.fst _ _).comp (q.sp P).toRingHom).comp (prV (E := E) (qv F P.1))

theorem qdf_at_val (q : QLoc hc n Q Θ) (P : Q) (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :
    ((q.at P x : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) = (x : Matrix (Fin n) (Fin n) _).map (qPi q P) := rfl

theorem qdf_pi_iA (q : QLoc hc n Q Θ) (P : Q) (e : E) : qPi q P (iA F E e) = q.phi P e := rfl

theorem qdf_phi_int (q : QLoc hc n Q Θ) (P : Q) (r : 𝓞 E) : q.phi P (r : E) ∈ (qv F P.1).adicCompletionIntegers F := by
  have h : Formalism.UG.inclE (F := F) ((qv F P.1).adicCompletion F) (r : E) ∈ Formalism.BasicNotions.intV E (qv F P.1) :=
    Subring.subset_closure (Or.inl ⟨⟨(r : E), r, rfl⟩, rfl⟩)
  exact ((q.sp_int P _).1 h).1

theorem qdf_pi_int (q : QLoc hc n Q Θ) (P : Q) {a : E ⊗[F] Formalism.L2.Herm.Af F} (ha : a ∈ Formalism.L2.Herm.intAf F E) :
    qPi q P a ∈ (qv F P.1).adicCompletionIntegers F := by
  have hle : Formalism.L2.Herm.intAf F E ≤
      (Formalism.BasicNotions.intV E (qv F P.1)).comap (Formalism.UG.prV (E := E) (qv F P.1)) := by
    refine Subring.closure_le.2 ?_
    rintro _ (⟨x, rfl⟩ | ⟨y, rfl⟩)
    · refine Subring.mem_comap.2 (Subring.subset_closure (Or.inl ⟨x, ?_⟩))
      simp [Formalism.UG.prV]
    · have hy : ∀ v, (y : Formalism.L2.Herm.Af F) v ∈ v.adicCompletionIntegers F := y.2
      refine Subring.mem_comap.2 (Subring.subset_closure (Or.inr ⟨⟨(y : Formalism.L2.Herm.Af F) (qv F P.1), hy _⟩, ?_⟩))
      simp [Formalism.UG.prV] <;> rfl
  exact ((q.sp_int P _).1 (hle ha)).1

theorem qdf_phi_unit (q : QLoc hc n Q Θ) (P : Q) {s : 𝓞 E} (hs : s ∉ P.1.asIdeal) :
    q.phi P (s : E) ≠ 0 ∧ (q.phi P (s : E))⁻¹ ∈ (qv F P.1).adicCompletionIntegers F := by
  have h1 : Valued.v (q.phi P (s : E)) ≤ 1 := qdf_phi_int q P s
  have h2 : ¬ Valued.v (q.phi P (s : E)) < 1 := fun h => hs ((q.sp_P P s).1 h)
  have hv : Valued.v (q.phi P (s : E)) = 1 := le_antisymm h1 (not_lt.1 h2)
  refine ⟨fun h0 => ?_, ?_⟩
  · rw [h0, map_zero] at hv
    exact zero_ne_one hv
  · show Valued.v (q.phi P (s : E))⁻¹ ≤ 1
    rw [map_inv₀, hv, inv_one]

theorem qdf_phi_intAt (q : QLoc hc n Q Θ) (P : Q) {a : E} (h : IntAt P.1 a) : q.phi P a ∈ (qv F P.1).adicCompletionIntegers F := by
  obtain ⟨r, s, hs, h⟩ := h
  have hu := qdf_phi_unit q P hs
  have hm : q.phi P (s : E) * q.phi P a = q.phi P (r : E) := by
    rw [← map_mul]
    exact congrArg (q.phi P) h
  have ha : q.phi P a = q.phi P (r : E) * (q.phi P (s : E))⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq₀ hu.1, mul_comm]
    exact hm
  rw [ha]
  exact mul_mem (qdf_phi_int q P r) hu.2

theorem qdf_gl_inv_val {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (A : GL (Fin n) R) :
    (((bc f A)⁻¹ : GL (Fin n) S) : Matrix (Fin n) (Fin n) S) = ((A⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R).map f := by
  rw [← map_inv]
  rfl

theorem qdf_frLat (q : QLoc hc n Q Θ) : FrLat ST SG q := by
  intro x p hx P
  have hN : p.deco.1.N = Formalism.UG.CS.globLat (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (stdLat E n) := by
    rw [← hx, rlc_decoOf_val hc n ST SG x.2]; rfl
  set fr := p.fr P with hfr

  have hfrN : ∀ w ∈ p.deco.1.N, ∀ i, q.phi P ((fr.symm w) i) ∈ (qv F P.1).adicCompletionIntegers F := by
    intro w hw i
    have h1 : fr (fr.symm w) ∈ p.deco.1.at P.1 := by
      rw [LinearEquiv.apply_symm_apply]
      exact (mem_locP P.1 _ w).2 ⟨1, P.1.isPrime.one_notMem, by rw [one_smul]; exact hw⟩
    have h2 : fr.symm w ∈ stdAt E n P.1 := (p.2 P (fr.symm w)).1 h1
    exact qdf_phi_intAt q P ((mem_localization_standardLattice P.1 _).1 h2 i)
  have hFinv : ((bc (q.phi P) (qGL n fr))⁻¹ : GL (Fin n) _) = bc (q.phi P) (qGL n fr.symm) := by
    rw [← map_inv]; congr 1
  constructor
  ·
    set xm : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F) := x.1 with hxm
    have key : ∀ z ∈ Formalism.L2.Herm.hatL (F := F) (Formalism.UG.CS.globLat (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (stdLat E n)), ∀ i,
        ((((bc (q.phi P) (qGL n fr))⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ (fun k => qPi q P (z k))) i ∈
          (qv F P.1).adicCompletionIntegers F := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨w, hw, rfl⟩ := hz
        intro i
        rw [hFinv]
        have e1 : ((bc (q.phi P) (qGL n fr.symm) : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ (fun k => qPi q P (iA F E (w k))) =
            fun k => q.phi P ((fr.symm w) k) := by
          funext k
          rw [← toGLm_mulVec fr.symm w]
          exact (RingHom.map_mulVec (q.phi P) _ w k).symm
        rw [e1]
        exact hfrN w (by rw [hN]; exact hw) i
      | zero =>
        intro i
        have e0 : (fun k => qPi q P ((0 : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) k)) = 0 := by funext k; simp
        rw [e0, Matrix.mulVec_zero]
        exact zero_mem _
      | add z1 z2 _ _ h1 h2 =>
        intro i
        have e2 : (fun k => qPi q P ((z1 + z2) k)) = (fun k => qPi q P (z1 k)) + (fun k => qPi q P (z2 k)) := by
          funext k; simp
        rw [e2, Matrix.mulVec_add]
        exact add_mem (h1 i) (h2 i)
      | smul a z1 _ h1 =>
        intro i
        have e2 : (fun k => qPi q P ((a • z1) k)) = qPi q P (a : E ⊗[F] Formalism.L2.Herm.Af F) • (fun k => qPi q P (z1 k)) := by
          funext k
          show qPi q P ((a : E ⊗[F] Formalism.L2.Herm.Af F) * z1 k) = _
          rw [map_mul]; rfl
        rw [e2, Matrix.mulVec_smul]
        exact mul_mem (qdf_pi_int q P a.2) (h1 i)
    intro i j
    have hz : (fun k => (xm : Matrix (Fin n) (Fin n) _) k j) ∈ Formalism.L2.Herm.hatL (F := F)
        (Formalism.UG.CS.globLat (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (stdLat E n)) := by
      refine (Formalism.UG.P.span_recovery_of_integral_adelic_approx Formalism.UG.P.integral_adele_approximation_holds F E (Fin n) (stdLat E n)
        (Module.Finite.iff_fg.2 (stdLat_lattice (E := E) (n := n)).fg) (stdLat_lattice (E := E) (n := n)).span_eq_top xm _).2 ?_
      have e3 : (((xm⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ
          fun k => (xm : Matrix (Fin n) (Fin n) _) k j) = fun k => iA F E ((Pi.single j (1 : E) : Sp E n) k) := by
        have : (fun k => (xm : Matrix (Fin n) (Fin n) _) k j) =
            (xm : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ Pi.single j (1 : E ⊗[F] Formalism.L2.Herm.Af F) := by
          funext k; rw [Matrix.mulVec_single_one]; rfl
        rw [this, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
        funext k
        by_cases hk : k = j
        · subst hk; simp
        · simp [Pi.single_apply, hk]
      rw [e3]
      exact Submodule.subset_span ⟨Pi.single j 1, by
        have := single_mem_stdLat (E := E) (n := n) j 1
        simpa using this, rfl⟩
    have := key _ hz i
    have e7 : ((((bc (q.phi P) (qGL n fr))⁻¹ * q.at P xm : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) i j) =
        ((((bc (q.phi P) (qGL n fr))⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ
          fun k => qPi q P ((xm : Matrix (Fin n) (Fin n) _) k j)) i := by
      rw [Units.val_mul, qdf_at_val]; rfl
    rw [e7]
    exact this
  ·
    intro i j
    have e0 : (((bc (q.phi P) (qGL n fr))⁻¹ * q.at P x)⁻¹ : GL (Fin n) _) = (q.at P x)⁻¹ * bc (q.phi P) (qGL n fr) := by
      rw [_root_.mul_inv_rev, inv_inv]
    rw [e0]
    have hcol : fr (Pi.single j 1) ∈ p.deco.1.at P.1 :=
      (p.2 P (Pi.single j 1)).2 ((mem_localization_standardLattice P.1 _).2 fun k => ⟨if k = j then 1 else 0, 1, P.1.isPrime.one_notMem, by
        by_cases hk : k = j <;> simp [Pi.single_apply, hk]⟩)
    obtain ⟨s, hs, hsN⟩ := (mem_locP P.1 _ _).1 hcol
    rw [hN] at hsN
    have hpull := (mem_globLat x.1 (s • fr (Pi.single j 1))).1 hsN
    obtain ⟨hne, hinv⟩ := qdf_phi_unit q P hs
    have e4 : ((((q.at P x)⁻¹ * bc (q.phi P) (qGL n fr) : GL (Fin n) _)) : Matrix (Fin n) (Fin n) _) i j =
        (q.phi P (s : E))⁻¹ * qPi q P (pullV x.1 (s • fr (Pi.single j 1)) i) := by
      have e5 : qPi q P (pullV x.1 (s • fr (Pi.single j 1)) i) =
          ((((q.at P x)⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ fun k => q.phi P ((s • fr (Pi.single j 1)) k)) i := by
        unfold pullV
        rw [RingHom.map_mulVec, ← qdf_at_inv, qdf_at_val]
        rfl
      rw [e5]
      have e6 : (fun k => q.phi P ((s • fr (Pi.single j 1)) k)) = q.phi P (s : E) • fun k => q.phi P ((fr (Pi.single j 1)) k) := by
        funext k
        simp [Submodule.smul_def, Algebra.smul_def]
      rw [e6, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hne, one_mul, Units.val_mul,
        Matrix.mul_apply]
      rw [Matrix.mulVec, dotProduct]
      refine Finset.sum_congr rfl fun k _ => ?_
      congr 1
    rw [e4]
    exact mul_mem hinv (qdf_pi_int q P (hpull i))

variable {H : Subgroup (GLG E n SG)}

def recClsFOf' (hS : DecoPtSurj hc n ST SG) (hQ : QOff (F := F) ST SG Q) (q : QLoc hc n Q Θ)
    (s : DecoFCl (K := K) n ST SG Q H Θ → DecoF E n ST SG Q)
    (hs : ∀ c, (Quotient.mk'' (s c) : DecoFCl (K := K) n ST SG Q H Θ) = c) : RecClsF hc n ST SG Q H q s :=
  recClsFOf hS hQ q (qdf_frLat q) qdf_frExists s hs

end QLat

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.XiHypOfThHyp
section
open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section Hyp

variable {X : Fields} {Pr : Primes X} {R : Ranks} {W : Wts X Pr.Word R} {Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))}
  {hQ : QE sel (mu : Chr X.F X.E X.K) = ∅} {m2 : ℕ} {al : ∀ j, j ≤ m2 + 1 → L.β j} {Am : Amb X} {u : Pr.Word}

theorem xiHyp_of_thHyp {σ₀ : X.K →+* ℂ} {G : ChainGlob W σ₀} (hm : R.m = m2 + 2) (hσ : Am.σ₀ = σ₀) (hPr : Pr.Ok)
    (hTh : ThHyp W Ch sel mu cst Am u m2)
    (hχ : ∀ i, i < R.m → ∀ (c : StCl W Λ u i) (c' : StCl W Λ u (i + 1)),
      Am.chiF (R.N i) (R.N (i + 1)) (repN W Λ u i c) (repN W Λ u (i + 1) c') ≠ 0)
    (hρ : RhoScal W Λ Ch sel mu cst G Am u) :
    XiHyp W Λ Ch sel mu cst Am u (refXi1 Ch sel mu cst L hQ m2 al u) G := by
  have hA : ∀ i, i < R.m → Am.AnaStep (R.N i) (R.N (i + 1)) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u) := by
    intro i hi
    rcases Nat.lt_or_ge m2 i with h | h
    · have e : i = m2 + 1 := by omega
      subst e
      have h2 := hTh.2.1
      rw [hm] at h2
      exact h2
    · exact hTh.1 i h
  exact
    { sig := hσ
      T_pos := (hPr.T_prime u).pos
      smooth := fun i hi => (hA i hi).2.1
      rat := fun i hi => (hA i hi).2.2
      chi_ne := hχ
      rho := hρ
      above := fun i hi p p' x => refXi1_above Ch sel mu cst L hQ m2 al u hm i hi p p' x }

end Hyp

end Formalism.L2.Col
end
end

