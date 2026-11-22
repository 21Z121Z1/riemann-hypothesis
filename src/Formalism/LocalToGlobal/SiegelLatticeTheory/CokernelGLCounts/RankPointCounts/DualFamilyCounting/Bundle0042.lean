import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0040
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NotIntDensOfSteps
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegralityUnderRingMap.MemIntegerOfIsIntegralMap
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle0007
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0075
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0035
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0039
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0028

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ImportsBis
section
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.OrthogonalProjections

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G6 Formalism.L2.SG.Pf.ProjectionDiscriminantModule

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V} {hc : IsCompl U (orthK h U)}
  {M T Λ₀ : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)}

theorem card_eq [FiniteDimensional K V] (hs : h.IsSymm) (h𝔭 : 𝔭.IsMaximal) (hM : IsLatIn U M)
    (hT : IsLatIn (orthK h U) T) (hgood : ∀ Λ, InFib h U 𝔭 M T Λ → Good hc M T 𝔭 Λ)
    (h0 : InFib h U 𝔭 M T Λ₀) :
    Nat.card {Λ // InFib h U 𝔭 M T Λ} =
      Nat.card {P : Module.End (𝓞 K) (DiscMod h (orthK h U) T 𝔭) // FP P} := by
  classical
  have G0 : Good hc M T 𝔭 Λ₀ := hgood Λ₀ h0
  have hd₀ : dualF h 𝔭 Λ₀ = Λ₀ := h0.2.1

  have hTW : ∀ {d : V}, d ∈ locF 𝔭 T → d ∈ orthK h U := by
    intro d hd
    have : d ∈ Λ₀ ⊓ (orthK h U).restrictScalars (𝓞 K) := by rw [G0.cW]; exact hd
    exact this.2
  have hTL : ∀ {Λ : Submodule (𝓞 K) V}, Good hc M T 𝔭 Λ → ∀ {d : V}, d ∈ locF 𝔭 T → d ∈ Λ := by
    intro Λ hG d hd
    have : d ∈ Λ ⊓ (orthK h U).restrictScalars (𝓞 K) := by rw [hG.cW]; exact hd
    exact this.1
  have hsW : ∀ {d : V}, d ∈ orthK h U → prO hc.symm d = d := fun hd =>
    (mem_W_of_prO_zero (hc := hc) (orth_projection_of_mem_compl hd)).2

  have hFP : ∀ Λ (hΛ : InFib h U 𝔭 M T Λ), FP (isoOf G0 (hgood Λ hΛ)) := by
    intro Λ hΛ
    have hG := hgood Λ hΛ
    refine fp_of (hc := hc) hs hd₀ hΛ.2.1 _ ?_
    intro b x' hx'
    obtain ⟨z, hz, hzb⟩ := G0.oW b b.2
    obtain ⟨w, hw, hwz⟩ := hG.oU (prO hc z) (G0.iU z hz)
    have hb : b = ⟨prO hc.symm z, G0.iW z hz⟩ := Subtype.ext hzb.symm
    rw [hb, isoOf_mk G0 hG hz hw hwz, Submodule.Quotient.eq, Submodule.mem_comap] at hx'
    have hd : (x' : V) - prO hc.symm w ∈ locF 𝔭 T := by simpa using hx'
    have hdW := hTW hd
    refine ⟨z, hz, w + ((x' : V) - prO hc.symm w), Λ.add_mem hw (hTL hG hd), hzb, ?_, ?_⟩
    · rw [map_add, hsW hdW]; abel
    · rw [map_add, orth_projection_of_mem_compl hdW, add_zero, hwz]
  have hglue : ∀ P, FP P → InFib h U 𝔭 M T (glue hc T 𝔭 Λ₀ P) := by
    intro P hP
    obtain ⟨N₀, hN₀, hloc⟩ := h0.1
    haveI : Finite (DiscMod h (orthK h U) T 𝔭) :=
      Formalism.L2.SG.Pf.ProjectionDiscriminantModule.discMod_finite hc h𝔭 hM hT hN₀ hloc G0.cW G0.iW G0.oW
    exact glue_mem hs h𝔭 hM hT G0 h0 hP (Finite.surjective_of_injective (FP.injective G0 hd₀ hP))
  have hleft : ∀ Λ (hΛ : InFib h U 𝔭 M T Λ), glue hc T 𝔭 Λ₀ (isoOf G0 (hgood Λ hΛ)) = Λ := by
    intro Λ hΛ
    have hG := hgood Λ hΛ
    ext x
    constructor
    · rintro ⟨b, hb, y, hy, c, hcy, hU, hP⟩
      obtain ⟨w, hw, hwy⟩ := hG.oU (prO hc y) (G0.iU y hy)
      have hc' : c = ⟨prO hc.symm y, G0.iW y hy⟩ := Subtype.ext hcy
      rw [hc', isoOf_mk G0 hG hy hw hwy, Submodule.Quotient.eq, Submodule.mem_comap] at hP
      have hd : (b : V) - prO hc.symm w ∈ locF 𝔭 T := by simpa using hP
      rw [hb] at hd
      exact mem_of_proj hG hw (hwy.trans hU) hd
    · intro hx
      obtain ⟨y, hy, hyx⟩ := G0.oU (prO hc x) (hG.iU x hx)
      exact ⟨⟨prO hc.symm x, hG.iW x hx⟩, rfl, y, hy, ⟨prO hc.symm y, G0.iW y hy⟩, rfl, hyx,
        (isoOf_mk G0 hG hy hx hyx.symm).symm⟩
  have hright : ∀ P (hP : FP P), isoOf G0 (hgood _ (hglue P hP)) = P := by
    intro P hP
    have hG := hgood _ (hglue P hP)
    refine LinearMap.ext fun q => ?_
    induction q using Submodule.Quotient.induction_on with
    | _ c =>
    obtain ⟨y, hy, hyc⟩ := G0.oW c c.2
    have hc' : c = ⟨prO hc.symm y, G0.iW y hy⟩ := Subtype.ext hyc.symm
    obtain ⟨x', hx'⟩ := Submodule.Quotient.mk_surjective _ (P (Submodule.Quotient.mk c))
    rw [hc'] at hx' ⊢
    have hmem := mem_glue_of (P := P) G0 hy x' hx'
    have hx'W : (x' : V) ∈ orthK h U := memW G0 x'.2
    have hUeq : prO hc (prO hc y + x') = prO hc y := by
      rw [map_add, prO_of_mem_U (prO_mem hc y), orth_projection_of_mem_compl hx'W, add_zero]
    rw [isoOf_mk G0 hG hy hmem hUeq, ← hx']
    congr 1
    apply Subtype.ext
    have e := prO_add hc (prO hc y)
    rw [prO_of_mem_U (prO_mem hc y)] at e
    have e0 : prO hc.symm (prO hc y) = 0 := by
      have := congrArg (fun v => v - prO hc y) e
      simpa using this
    simp only [map_add, e0, zero_add, hsW hx'W]
  exact Nat.card_congr
    { toFun := fun Λ => ⟨isoOf G0 (hgood Λ.1 Λ.2), hFP Λ.1 Λ.2⟩
      invFun := fun P => ⟨glue hc T 𝔭 Λ₀ P.1, hglue P.1 P.2⟩
      left_inv := fun Λ => Subtype.ext (hleft Λ.1 Λ.2)
      right_inv := fun P => Subtype.ext (hright P.1 P.2) }

end Formalism.L2.SG.Pf.OrthogonalProjections
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LocGlobInt
section
open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups ValuativeRel

noncomputable section

namespace Formalism.L2.SG.Pf.Cnt.DualityBasisChange

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem mem_integer_iff_vle {K : Type} [Field K] [ValuativeRel K] (x : K) : x ∈ 𝒪[K] ↔ x ≤ᵥ 1 := by
  rw [Valuation.mem_integer_iff]
  exact (Valuation.vle_one_iff (v := valuation K)).symm

theorem mem_OF_of_loc (D : Formalism.BasicNotions.D7) (s : D.host.F)
    (hs : ∀ p : PlF D, (D.s.atP p).ιE (algebraMap D.host.F D.host.E s) ∈ (D.s.atP p).O) :
    s ∈ (algebraMap (𝓞 D.host.F) D.host.F).range := by
  refine IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one D.host.F s fun p => ?_
  have h1 := hs p
  rw [(D.s.atP p).compat] at h1
  have hint := ((D.s.atP p).O_def _).1 h1
  have hnt : Nontrivial (D.s.atP p).Ep :=
    Module.nontrivial_of_finrank_pos (R := (D.s.atP p).Fp) (by rw [(D.s.atP p).rank]; norm_num)
  have hinj : Function.Injective (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep) := by
    haveI := hnt; exact (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep).injective
  have h2 : (D.s.atP p).ιF s ∈ 𝒪[(D.s.atP p).Fp] :=
    PI.IntegralDiscriminantMembership.mem_integer_of_isIntegral ((isIntegral_algebraMap_iff hinj).1 hint)
  rw [mem_integer_iff_vle, ← map_one (D.s.atP p).ιF, (D.s.atP p).val, map_one] at h2
  exact h2

theorem locGlobIntE : LocGlobIntE := by
  intro D x hx
  have hcjO : ∀ p : PlF D, (D.s.atP p).ιE (star x) ∈ (D.s.atP p).O := fun p => by
    rw [PI.UnitaryGroupMassFormula.CntFormula.star_eq_conjF, ← (D.s.atP p).cj_ιE, (D.s.atP p).O_def]
    exact ((D.s.atP p).O_def _).1 (hx p) |>.map ((D.s.atP p).cj.toAlgHom.restrictScalars 𝒪[(D.s.atP p).Fp])
  obtain ⟨t, ht⟩ := (D.sp.cm.fixed (x + star x)).1 (by rw [star_add, star_star, add_comm])
  obtain ⟨n, hn⟩ := (D.sp.cm.fixed (x * star x)).1 (by rw [star_mul, star_star, mul_comm])
  obtain ⟨t', ht'⟩ := mem_OF_of_loc D t fun p => by
    rw [ht, map_add]; exact (D.s.atP p).O.add_mem (hx p) (hcjO p)
  obtain ⟨n', hn'⟩ := mem_OF_of_loc D n fun p => by
    rw [hn, map_mul]; exact (D.s.atP p).O.mul_mem (hx p) (hcjO p)

  have hT : IsIntegral ℤ (x + star x) := by
    rw [← ht, ← ht']
    exact map_isIntegral_int (algebraMap D.host.F D.host.E) (map_isIntegral_int _ (RingOfIntegers.isIntegral t'))
  have hN : IsIntegral ℤ (x * star x) := by
    rw [← hn, ← hn']
    exact map_isIntegral_int (algebraMap D.host.F D.host.E) (map_isIntegral_int _ (RingOfIntegers.isIntegral n'))
  set a : 𝓞 D.host.E := ⟨x + star x, hT⟩
  set b : 𝓞 D.host.E := ⟨x * star x, hN⟩
  have hx' : IsIntegral (𝓞 D.host.E) x := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.C a * Polynomial.X + Polynomial.C b, by monicity!, ?_⟩
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C]
    show x ^ 2 - (x + star x) * x + x * star x = 0
    ring
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hx'
  exact Submodule.mem_one.2 ⟨y, hy⟩

theorem not_integral_density_of_self_dual (h1 : LocSelfDual) (hF : FrameBasisL) : NotIntDens :=
  notIntDens_of_steps h1 hF locGlobIntE

end Formalism.L2.SG.Pf.Cnt.DualityBasisChange
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NOfibCut
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Matrix
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.Pf.NcReal.JX Formalism.L2.SG.TermOp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Defs

variable {D : D7} (X : HidaSetting D)

abbrev BV : Type := ∀ q : CBlk D.R.rS, CSpc (InfinitePlace X.B.I.F) D.R.k q

def iQ (D : D7) (b a : Fin D.R.rS) : Set D.host.E :=
  ((aaD D b * (aaD D a)⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Set D.host.E)

def iP (D : D7) (b a : Fin D.R.rS) : Set D.host.E :=
  ((aaD D b * aaD D a : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Set D.host.E)

def pW (y : (VS D).V) : (VS D).V :=
  y - ∑ c, (VS D).hT (X.fY c) y • X.eX c - ∑ c, (VS D).hT (X.eX c) y • X.fY c

def InW (y : (VS D).V) : Prop := ∀ c, (VS D).hT (X.eX c) y = 0 ∧ (VS D).hT (X.fY c) y = 0

def Xq (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E :=
  fun b a => (VS D).hT (X.fY b) (n (X.eX a))

def Aq (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E :=
  fun b a => (VS D).hT (X.fY b) (n (X.fY a))

def Mq (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E :=
  (Xq X n)⁻¹ * Aq X n

def xq (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (b : Fin D.R.rS) : (VS D).V := pW X (n.symm (X.fY b))

def Gq (D : D7) (xs : Fin D.R.rS → (VS D).V) : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E :=
  fun b c => (VS D).hT (xs b) (xs c)

def Gp (D : D7) (X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (xs : Fin D.R.rS → (VS D).V) :
    Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E :=
  X0⁻¹ * Gq D xs * (X0⁻¹)ᴴ

def DataOK (X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (xs : Fin D.R.rS → (VS D).V)
    (M : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) : Prop :=
  (∀ b a : Fin D.R.rS, a < b → X0 b a = 0) ∧ (∀ a, X0 a a = 1) ∧ (∀ b, InW X (xs b)) ∧ M + Mᴴ = -Gp D X0 xs

def LatQ (X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (xs : Fin D.R.rS → (VS D).V)
    (M : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) : Prop :=
  (∀ b a : Fin D.R.rS, b < a → X0 b a ∈ iQ D b a) ∧ (∀ b, xs b ∈ aaLb X b) ∧ ∀ b a, M b a ∈ iP D b a

variable (u : D.what₂.Word)

def NFl (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) : Prop :=
  n ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧
    (∀ j, ∀ x ∈ Xflag (lf D (X.Fu u)) (j + 1), n x - x ∈ Xflag (lf D (X.Fu u)) j) ∧
    ∀ x ∈ orth (VS D) (Xsp (lf D (X.Fu u))), n x - x ∈ Xsp (lf D (X.Fu u))

def blkQ (X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (xs : Fin D.R.rS → (VS D).V)
    (M : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) :
    ∀ p : CBlk D.R.rS, CSpc (InfinitePlace X.B.I.F) D.R.k p
  | Sum.inl (Sum.inl p) => embV X (X0 p.1.1 p.1.2)
  | Sum.inl (Sum.inr b) => rowV X u (xs b)
  | Sum.inr (Sum.inl p) => fun v =>
      (embS D (X.pl v) (M p.1.1 p.1.2) - star (embS D (X.pl v) (M p.1.2 p.1.1))) / 2
  | Sum.inr (Sum.inr a) => fun v => (embS D (X.pl v) (M a a)).im

open scoped Classical in

def theta (D : D7) : D.host.E :=
  if h : ∃ t : D.host.E, IsIntegral ℤ t ∧ t + D.host.conj t = 1 then h.choose else 0

def Xc (x : BV X) (v : InfinitePlace X.B.I.F) :
    Matrix (Fin D.R.rS) (Fin D.R.rS) ℂ :=
  fun b a => if h : b < a then x (Sum.inl (Sum.inl ⟨(b, a), h⟩)) v else if b = a then 1 else 0

def Gc (x : BV X) (v : InfinitePlace X.B.I.F) :
    Matrix (Fin D.R.rS) (Fin D.R.rS) ℂ :=
  fun b c => (∑ j : Fin D.R.k, x (Sum.inl (Sum.inr b)) v (Fin.castSucc j) *
      star (x (Sum.inl (Sum.inr c)) v (Fin.castSucc j))) -
    x (Sum.inl (Sum.inr b)) v (Fin.last D.R.k) * star (x (Sum.inl (Sum.inr c)) v (Fin.last D.R.k)) /
      (((D.mem u).A.T : ℕ) : ℂ)

def Hc (x : BV X) (v : InfinitePlace X.B.I.F) :
    Matrix (Fin D.R.rS) (Fin D.R.rS) ℂ :=
  (Xc X x v)⁻¹ * Gc X u x v * ((Xc X x v)⁻¹)ᴴ

def tauQ : ∀ p : CBlk D.R.rS, BV X → CSpc (InfinitePlace X.B.I.F) D.R.k p
  | Sum.inl (Sum.inl _) => fun _ => 0
  | Sum.inl (Sum.inr _) => fun _ => 0
  | Sum.inr (Sum.inl p) => fun x v => Hc X u x v p.1.1 p.1.2 / 2
  | Sum.inr (Sum.inr a) => fun x v => -((Hc X u x v a a).re * (embS D (X.pl v) (theta D)).im)

end Defs

def NOratC : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (s : X.B.I.Ginf),
    s ∈ Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u ↔
      ∃ (x : X.B.I.GA) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V), RatLink X x n ∧ x.1 = s ∧
        n ∈ NLam (VS D).L0 (lf D (X.Fu u))

def DictGram : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V),
    NFl X u n → DataOK X (Xq X n) (xq X n) (Mq X n)

def DictLat : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V),
    NFl X u n → (Formalism.HermitianLatticesTheory.gmap n (VS D).L0 = (VS D).L0 ↔ LatQ X (Xq X n) (xq X n) (Mq X n))

def DictEx : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E)
    (xs : Fin D.R.rS → (VS D).V) (M : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E), DataOK X X0 xs M →
    ∃ n : (VS D).V ≃ₗ[D.host.E] (VS D).V, NFl X u n ∧ Xq X n = X0 ∧ xq X n = xs ∧ Mq X n = M

def DictPlace : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (x : X.B.I.GA) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V),
    RatLink X x n → NFl X u n → blk X u x.1 = blkQ X u (Xq X n) (xq X n) (Mq X n)

def FibQ : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E)
    (xs : Fin D.R.rS → (VS D).V) (M : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E), DataOK X X0 xs M →
    ((∀ p, blkQ X u X0 xs M p - tauQ X u p (blkQ X u X0 xs M) ∈ cLat X u p) ↔ LatQ X X0 xs M)

def FibOnto : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (x : BV X),
    (∀ p, x p - tauQ X u p x ∈ cLat X u p) →
      ∃ (X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (xs : Fin D.R.rS → (VS D).V)
        (M : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E), DataOK X X0 xs M ∧ blkQ X u X0 xs M = x

def ThetaEx : Prop :=
  ∀ D : D7, ∃ t : D.host.E, IsIntegral ℤ t ∧ t + D.host.conj t = 1

theorem tauQ_lower {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (p : CBlk D.R.rS)
    (x x' : BV X) (h : ∀ q, cHgt q < cHgt p → x q = x' q) :
    tauQ X u p x = tauQ X u p x' := by
  rcases p with (p | b) | (p | a)
  · rfl
  · rfl
  all_goals
    have hX : ∀ q, x (Sum.inl q) = x' (Sum.inl q) := by
      intro q
      apply h
      rcases q with q | c
      · have := q.1.2.isLt
        simp only [cHgt]
        omega
      · have := c.isLt
        simp only [cHgt]
        omega
    have hH : Hc X u x = Hc X u x' := by
      funext v
      have hXc : Xc X x v = Xc X x' v := by
        funext i j
        simp only [Xc, hX]
      have hGc : Gc X u x v = Gc X u x' v := by
        funext i j
        simp only [Gc, hX]
      simp only [Hc, hXc, hGc]
    simp only [tauQ]
    rw [hH]

theorem nofibLat_of (hR : NOratC) (hG : DictGram) (hL : DictLat) (hE : DictEx) (hP : DictPlace) (hF : FibQ)
    (hO : FibOnto) : NOfibLat := by
  intro D X u
  refine ⟨tauQ X u, fun p x x' h => tauQ_lower X u p x x' h, fun x => ⟨?_, ?_⟩⟩
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨xA, n, hlink, hx1, hn⟩ := (hR X u s).1 hs
    have hNF : NFl X u n := ⟨hn.1.1, hn.2.1, hn.2.2⟩
    have hD := hG X u n hNF
    have hLat := (hL X u n hNF).1 hn.1.2
    rw [← hx1, hP X u xA n hlink hNF]
    exact (hF X u _ _ _ hD).2 hLat
  · intro hx
    obtain ⟨X0, xs, M, hD, rfl⟩ := hO X u x hx
    have hLat := (hF X u X0 xs M hD).1 hx
    obtain ⟨n, hNF, h1, h2, h3⟩ := hE X u X0 xs M hD
    subst h1 h2 h3
    have hgm := (hL X u n hNF).2 hLat
    have hn : n ∈ NLam (VS D).L0 (lf D (X.Fu u)) := ⟨⟨hNF.1, hgm⟩, hNF.2.1, hNF.2.2⟩
    obtain ⟨xA, hlink⟩ := ratPt_holds D X n hNF.1
    exact ⟨xA.1, (hR X u xA.1).2 ⟨xA, n, hlink, rfl, hn⟩, hP X u xA n hlink hNF⟩

end Formalism.L2.SG.Pf.NcReal.JX.NOf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.RowParseval
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX.CovB

open Formalism.L2.SG.HidaSetting Formalism.MainNotions.S Formalism.L2.SG.Pf.NcReal.JX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def gC {D : D7} (u : D.what₂.Word) (c : Fin (D.R.k + 1)) : ℂ :=
  if c.val < D.R.k then 1 else -(1 / ((Formalism.L2.SG.RealObj.Tw u : ℝ) : ℂ))

def RowParseval : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (x y : (VS D).V),
    (∀ a, (VS D).hT (X.eX a) x = 0 ∧ (VS D).hT (X.fY a) x = 0) →
    (∀ a, (VS D).hT (X.eX a) y = 0 ∧ (VS D).hT (X.fY a) y = 0) →
    ∀ v : InfinitePlace X.B.I.F,
      ∑ c, rowV X u x v c * star (rowV X u y v c) * gC u c = X.B.I.φ v (X.ιE.symm ((VS D).hT x y))

def RowRank : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (b : Fin D.R.rS),
    Nonempty (Module.Basis (Fin (Module.finrank ℚ D.host.E * (D.R.k + 1))) ℤ ((aaLbS X b).restrictScalars ℤ))

def TraceRe : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (t : D.host.E),
    ∑ v : InfinitePlace X.B.I.F, (X.B.I.φ v (X.ιE.symm t)).re = ((Algebra.trace ℚ D.host.E t : ℚ) : ℝ) / 2

end Formalism.L2.SG.Pf.NcReal.JX.CovB
end
end

