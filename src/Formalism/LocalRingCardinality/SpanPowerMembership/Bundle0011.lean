import Formalism.LocalRingCardinality.Lemmas
import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle0001
import Formalism.LocalRingCardinality.SpanPowerMembership.NZColC
import Formalism.LocalRingCardinality.SpanPowerMembership.TwCore

-- bundled from Formalism.LocalRingCardinality.SpanPowerMembership.NZColA
section
noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open NumberField Formalism.MainNotions.G

structure GatBasis (D : D7) where
  embW : ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    D.what₂.LL →+* (D.gat u w hg).Kf
  embW_int : ∀ u w hg (x : D.what₂.LL), (0 : WithTop ℤ) ≤ D.what₂.places.val w x ↔
    embW u w hg x ∈ Set.range (algebraMap (D.gat u w hg).O (D.gat u w hg).Kf)
  bas : ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    ((D.fm u).lat 0).ι → (D.gat u w hg).Fn
  bas_li : ∀ u w hg, LinearIndependent (D.gat u w hg).Kf (bas u w hg)
  bas_span : ∀ u w hg, Submodule.span (D.gat u w hg).O (Set.range (bas u w hg)) = (D.gat u w hg).M

namespace GatBasis

variable {D : D7} (B : GatBasis D)

def cmp (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) : ((D.fm u).lat 0).V →+ (D.gat u w hg).Fn where
  toFun x := ∑ a, B.embW u w hg (((D.fm u).lat 0).b.repr x a) • B.bas u w hg a
  map_zero' := by simp
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]

theorem cmp_apply (u w hg) (x : ((D.fm u).lat 0).V) :
    B.cmp u w hg x = ∑ a, B.embW u w hg (((D.fm u).lat 0).b.repr x a) • B.bas u w hg a := rfl

theorem cmp_smul (u w hg) (r : D.what₂.LL) (x : ((D.fm u).lat 0).V) :
    B.cmp u w hg (r • x) = B.embW u w hg r • B.cmp u w hg x := by
  rw [cmp_apply, cmp_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, mul_smul]

theorem cmp_basis (u w hg) (a : ((D.fm u).lat 0).ι) : B.cmp u w hg (((D.fm u).lat 0).b a) = B.bas u w hg a := by
  rw [cmp_apply, Finset.sum_eq_single a]
  · rw [Module.Basis.repr_self, Finsupp.single_eq_same, map_one, one_smul]
  · intro c _ hc
    rw [Module.Basis.repr_self, Finsupp.single_eq_of_ne hc, map_zero, zero_smul]
  · intro h; exact absurd (Finset.mem_univ a) h

theorem int_mem (u w hg) (r : 𝓞 D.what₂.LL) :
    B.embW u w hg (r : D.what₂.LL) ∈ Set.range (algebraMap (D.gat u w hg).O (D.gat u w hg).Kf) := by
  rw [← B.embW_int, D.val_nonneg_iff]
  exact (D.plEq w).valuation_le_one r

def toCmp (hstd : ∀ u, ((D.fm u).lat 0).L = Submodule.span (𝓞 D.what₂.LL) (Set.range ((D.fm u).lat 0).b)) :
    LatCmp D where
  embW := B.embW
  embW_int := B.embW_int
  cmp := B.cmp
  cmp_smul := B.cmp_smul
  cmp_li u w hg := by
    have : (fun a => B.cmp u w hg (((D.fm u).lat 0).b a)) = B.bas u w hg := funext (B.cmp_basis u w hg)
    rw [this]; exact B.bas_li u w hg
  cmp_M u w hg := by
    rw [← B.bas_span u w hg]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      rw [SetLike.mem_coe, hstd u] at hx
      induction hx using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨a, rfl⟩ := hy
        rw [B.cmp_basis]; exact Submodule.subset_span ⟨a, rfl⟩
      | zero => rw [map_zero]; exact Submodule.zero_mem _
      | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
      | smul r y _ hy =>
        obtain ⟨o, ho⟩ := B.int_mem u w hg r
        have h1 : r • y = (r : D.what₂.LL) • y := (algebraMap_smul D.what₂.LL r y).symm
        rw [h1, B.cmp_smul, ← ho, algebraMap_smul]
        exact Submodule.smul_mem _ o hy
    · rw [Submodule.span_le]
      rintro _ ⟨a, rfl⟩
      refine Submodule.subset_span ⟨((D.fm u).lat 0).b a, ?_, B.cmp_basis u w hg a⟩
      rw [SetLike.mem_coe, hstd u]
      exact Submodule.subset_span ⟨a, rfl⟩

include B in

theorem d_eq (u w hg) (hinj : Function.Injective (algebraMap (D.gat u w hg).O (D.gat u w hg).Kf)) :
    (D.gat u w hg).d = Fintype.card ((D.fm u).lat 0).ι := by
  unfold GAtP.d
  rw [← B.bas_span u w hg]
  refine finrank_span_eq_card ?_
  have : FaithfulSMul (D.gat u w hg).O (D.gat u w hg).Kf := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  exact (B.bas_li u w hg).restrict_scalars' (D.gat u w hg).O

end GatBasis

end Formalism.BasicNotions.Examples₂.NZ
end
end

-- bundled from Formalism.LocalRingCardinality.SpanPowerMembership.NZColD
section
noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open NumberField IsDedekindDomain Formalism.MainNotions.G Classical

section Gen

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module (𝓞 K) V]

def locS (w : HeightOneSpectrum (𝓞 K)) (B : Submodule (𝓞 K) V) : Submodule (𝓞 K) V where
  carrier := {x | InLoc w B x}
  add_mem' := by
    rintro a b ⟨s, hs, h1⟩ ⟨t, ht, h2⟩
    refine ⟨s * t, fun h => (w.isPrime.mem_or_mem h).elim hs ht, ?_⟩
    rw [smul_add]
    refine B.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact B.smul_mem _ h1
    · rw [mul_smul]; exact B.smul_mem _ h2
  zero_mem' := ⟨1, fun h => w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by simp⟩
  smul_mem' := by
    rintro r a ⟨s, hs, h1⟩
    exact ⟨s, hs, by rw [smul_comm]; exact B.smul_mem r h1⟩

theorem mem_locS (w : HeightOneSpectrum (𝓞 K)) (B : Submodule (𝓞 K) V) (x : V) : x ∈ locS w B ↔ InLoc w B x := Iff.rfl

theorem locS_sat (w : HeightOneSpectrum (𝓞 K)) (B : Submodule (𝓞 K) V) (s : 𝓞 K) (hs : s ∉ w.asIdeal) (x : V)
    (h : s • x ∈ locS w B) : x ∈ locS w B := by
  obtain ⟨t, ht, h1⟩ := h
  exact ⟨t * s, fun h => (w.isPrime.mem_or_mem h).elim ht hs, by rwa [mul_smul]⟩

theorem exists_pow_val (v : HeightOneSpectrum (𝓞 K)) (b : 𝓞 K) (hb : b ≠ 0) :
    ∃ m : ℕ, ∀ a ∈ v.asIdeal ^ m, v.valuation K (algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K b) ≤ 1 := by
  refine ⟨(Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {b} : Ideal (𝓞 K))).factors, fun a ha => ?_⟩
  rw [map_div₀, v.valuation_of_algebraMap, v.valuation_of_algebraMap]
  have h0 : 0 < v.intValuation b := by
    rw [v.intValuation_if_neg hb]; exact WithZero.exp_pos
  rw [div_le_one₀ h0, v.intValuation_if_neg hb]
  exact (v.intValuation_le_pow_iff_mem a _).mpr ha

theorem finite_over (t : 𝓞 K) (ht : t ≠ 0) : {v : HeightOneSpectrum (𝓞 K) | t ∈ v.asIdeal}.Finite := by
  have h : Ideal.span {t} ≠ 0 := by rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact ht
  exact (Ideal.finite_factors h).subset fun v hv => Ideal.dvd_span_singleton.mpr hv

variable [Module K V] [IsScalarTower (𝓞 K) K V]

theorem smul_eq_div (a b : 𝓞 K) (hb : b ≠ 0) (x : V) :
    a • x = (algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K b) • (b • x) := by
  have hbK : algebraMap (𝓞 K) K b ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hb
  rw [← algebraMap_smul K b, smul_smul, div_mul_cancel₀ _ hbK, algebraMap_smul]

end Gen

variable {D : D7} (c : LatCmp D)

structure NuData (c : LatCmp D) where
  S : ℕ → Prop
  S_fin : {p | S p}.Finite
  NPf : ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    Submodule (D.gat u w hg).O (D.gat u w hg).Fn

  exists_residueChar_pow_smul_mem : ∀ u w hg, ∃ N : ℕ, ∀ y ∈ DV.MramL D u,
    ((D.what₂.places.resChar w : ℕ) : (D.gat u w hg).O) ^ N • c.cmpN u w hg y ∈ NPf u w hg

  T_abs : ∀ u (w : D.what₂.places.Pl), D.what₂.places.resChar w = (D.mem u).A.T → ∀ x : (D.div.Nu u).V,
    ∃ m : ℕ, ∀ a ∈ (D.plEq w).asIdeal ^ m, D.nuIn u (a • x) ∈ LT.Nlam D u w

variable {c} (N : NuData c)

theorem int_mem_intW (w : D.what₂.places.Pl) (r : 𝓞 D.what₂.LL) : (r : D.what₂.LL) ∈ intW D.what₂.places w :=
  (D.val_nonneg_iff w _).2 ((D.plEq w).valuation_le_one r)

def atT (u : D.what₂.Word) (w : D.what₂.places.Pl) : Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V where
  carrier := {x | D.nuIn u x ∈ LT.Nlam D u w}
  add_mem' := by
    intro a b ha hb
    show D.nuIn u (a + b) ∈ LT.Nlam D u w
    rw [map_add]; exact Submodule.add_mem _ ha hb
  zero_mem' := by
    show D.nuIn u 0 ∈ LT.Nlam D u w
    rw [map_zero]; exact Submodule.zero_mem _
  smul_mem' := by
    intro r a ha
    show D.nuIn u (r • a) ∈ LT.Nlam D u w
    rw [← algebraMap_smul D.what₂.LL r a, map_smul]
    exact (LT.Nlam D u w).smul_mem (⟨_, int_mem_intW w r⟩ : intW D.what₂.places w) ha

include N in

def srv (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V where
  carrier := {x | c.cmpN u w hg x ∈ N.NPf u w hg}
  add_mem' := by
    intro a b ha hb
    show c.cmpN u w hg (a + b) ∈ N.NPf u w hg
    rw [map_add]; exact Submodule.add_mem _ ha hb
  zero_mem' := by
    show c.cmpN u w hg 0 ∈ N.NPf u w hg
    rw [map_zero]; exact Submodule.zero_mem _
  smul_mem' := by
    intro r a ha
    show c.cmpN u w hg (r • a) ∈ N.NPf u w hg
    obtain ⟨o, ho⟩ := (c.embW_val u w hg _).1 ((D.plEq w).valuation_le_one r)
    rw [← algebraMap_smul D.what₂.LL r a, c.cmpN_smul, ← ho, algebraMap_smul]
    exact Submodule.smul_mem _ o ha

def cond (u : D.what₂.Word) (w : D.what₂.places.Pl) : Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V :=
  if D.what₂.places.resChar w = (D.mem u).A.T then atT u w
  else if h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) ∧ N.S (D.what₂.places.resChar w) then srv N u w h.1
  else locS (D.plEq w) (DV.MramL D u)

def nuLat (u : D.what₂.Word) : Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V :=
  glue fun v => cond N u (D.plEq.symm v)

theorem inv_mem_intW (w : D.what₂.places.Pl) (s : 𝓞 D.what₂.LL) (hs : s ∉ (D.plEq w).asIdeal) :
    (algebraMap (𝓞 D.what₂.LL) D.what₂.LL s)⁻¹ ∈ intW D.what₂.places w ∧ algebraMap (𝓞 D.what₂.LL) D.what₂.LL s ≠ 0 := by
  have hv : (D.plEq w).valuation D.what₂.LL (algebraMap (𝓞 D.what₂.LL) D.what₂.LL s) = 1 :=
    ((D.plEq w).valuation_eq_one_iff_notMem).2 hs
  have hs0 : algebraMap (𝓞 D.what₂.LL) D.what₂.LL s ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hv
    exact zero_ne_one hv
  exact ⟨(D.val_nonneg_iff w _).2 (by rw [map_inv₀, hv, inv_one]), hs0⟩

theorem cond_sat (u : D.what₂.Word) (w : D.what₂.places.Pl) (s : 𝓞 D.what₂.LL) (hs : s ∉ (D.plEq w).asIdeal)
    (x : (D.div.Nu u).V) (h : s • x ∈ cond N u w) : x ∈ cond N u w := by
  obtain ⟨hinv, hs0⟩ := inv_mem_intW w s hs
  have hx : x = (algebraMap (𝓞 D.what₂.LL) D.what₂.LL s)⁻¹ • (s • x) := by
    rw [← algebraMap_smul D.what₂.LL s, smul_smul, inv_mul_cancel₀ hs0, one_smul]
  unfold cond at h ⊢
  split_ifs at h ⊢ with h1 h2
  · show D.nuIn u x ∈ LT.Nlam D u w
    rw [hx, map_smul]
    exact (LT.Nlam D u w).smul_mem (⟨_, hinv⟩ : intW D.what₂.places w) h
  · show c.cmpN u w h2.1 x ∈ N.NPf u w h2.1
    obtain ⟨o, ho⟩ := (c.embW_val u w h2.1 _).1 ((D.val_nonneg_iff w _).1 hinv)
    rw [hx, c.cmpN_smul, ← ho, algebraMap_smul]
    exact Submodule.smul_mem _ o h
  · exact locS_sat _ _ s hs x h

theorem resChar_mem (w : D.what₂.places.Pl) : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) ∈ (D.plEq w).asIdeal := by
  rw [← (D.plEq w).valuation_lt_one_iff_mem (K := D.what₂.LL), D.val_resChar' w, ← WithZero.exp_zero, WithZero.exp_lt_exp]
  have := D.what₂.places.ramIdx_pos w
  omega

variable (hspan : ∀ u, Submodule.span D.what₂.LL (DV.MramL D u : Set (D.div.Nu u).V) = ⊤)

theorem locLe_zero_iff {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module (𝓞 K) V]
    (w : HeightOneSpectrum (𝓞 K)) (A B : Submodule (𝓞 K) V) : DV.LocLe w 0 A B ↔ ∀ x ∈ A, InLoc w B x := by
  unfold DV.LocLe InLoc
  rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]

theorem inLoc_of_mem {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module (𝓞 K) V]
    (w : HeightOneSpectrum (𝓞 K)) (A : Submodule (𝓞 K) V) {x : V} (h : x ∈ A) : InLoc w A x :=
  ⟨1, fun h => w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by rwa [one_smul]⟩

end Formalism.BasicNotions.Examples₂.NZ
end
end

-- bundled from Formalism.LocalRingCardinality.SpanPowerMembership.NZColH
section
noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.ND

section

variable (ι : Type) [Fintype ι] [DecidableEq ι]

abbrev MuN : Type := EuclideanSpace ℂ ι

def eE : MuN ι ≃ₗ[ℂ] FK ι := (EuclideanSpace.equiv ι ℂ).toLinearEquiv.trans (eF ι)

theorem eE_apply (φ : MuN ι) (c : ι) (y : Unit) : eE ι φ c y = φ c := rfl

theorem inner_eE (φ ψ : MuN ι) : inner ℂ φ ψ = ipS ι (eE ι φ) (eE ι ψ) := by
  rw [ipS_apply, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [eE_apply, eE_apply, RCLike.inner_apply]
  exact mul_comm _ _

variable {ι} {LL : Type} [Field LL] [NumberField LL] [StarRing LL] (σ : LL →+* ℂ)

def jE : (ι → LL) →ₛₗ[σ] MuN ι where
  toFun x := (eE ι).symm (slK σ x)
  map_add' x y := by rw [map_add, map_add]
  map_smul' c x := by rw [LinearMap.map_smulₛₗ, map_smul]

theorem eE_jE (x : ι → LL) : eE ι (jE σ x) = slK σ x := (eE ι).apply_symm_apply _

theorem jE_basis : LinearIndependent ℂ (fun i => jE σ ((stdHLat LL ι).b i)) ∧
    Submodule.span ℂ (Set.range (fun i => jE σ ((stdHLat LL ι).b i))) = ⊤ := by
  obtain ⟨h1, h2⟩ := slK_basis (ι := ι) σ
  have h : (fun i => jE σ ((stdHLat LL ι).b i)) = (eE ι).symm ∘ fun i => slK σ ((stdHLat LL ι).b i) := rfl
  rw [h]
  refine ⟨h1.map' _ (LinearEquiv.ker _), ?_⟩
  rw [Set.range_comp]
  have h3 := Submodule.map_span (eE ι).symm.toLinearMap (Set.range fun i => slK σ ((stdHLat LL ι).b i))
  rw [h2, Submodule.map_top, LinearEquiv.range] at h3
  exact h3.symm

theorem norm_jE (x : ι → LL) :
    Formalism.HermitianLatticesTheory.normAt (stdHLat LL ι).b (stdHLat LL ι).X (InfinitePlace.mk σ) x = ‖jE σ x‖ := by
  rw [normAt_std, EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [InfinitePlace.norm_embedding_eq, InfinitePlace.apply]
  rfl

end

section Rec

variable {R : Ranks} {Tau : Type} [Fintype Tau] (hc : Tau → HCParam R) (K : ClsPkg) (T : ℕ) [hT : Fact T.Prime]
  (Dst : ℝ) (hD : 0 < Dst) (du : ℕ) (hdu : 0 < du) (Gam : ℝ) (hG : 1 < Gam)

def eMuN (hT2 : T ≠ 2) : MuN (K.cls 0) ≃ₗ[ℂ] (atTN hc K T Dst hD du hdu Gam hG).Mram :=
  (eE (K.cls 0)).trans (LinearEquiv.ofTop _ (atTN_Mram hc K T Dst hD du hdu Gam hG hT2)).symm

theorem eMuN_coe (hT2 : T ≠ 2) (φ : MuN (K.cls 0)) :
    ((eMuN hc K T Dst hD du hdu Gam hG hT2 φ : (atTN hc K T Dst hD du hdu Gam hG).Mram) : FK (K.cls 0)) =
      eE (K.cls 0) φ := rfl

def eCuN : MuN (K.cls 0) ≃ₗ[ℂ] (atTN hc K T Dst hD du hdu Gam hG).Mu0 :=
  (eE (K.cls 0)).trans (LinearEquiv.ofTop (⊤ : Submodule ℂ (FK (K.cls 0))) rfl).symm

theorem eCuN_coe (φ : MuN (K.cls 0)) :
    ((eCuN hc K T Dst hD du hdu Gam hG φ : (atTN hc K T Dst hD du hdu Gam hG).Mu0) : FK (K.cls 0)) =
      eE (K.cls 0) φ := rfl

end Rec

end Formalism.BasicNotions.Examples₂.NZ
end
end

-- bundled from Formalism.LocalRingCardinality.SpanPowerMembership.TiesGen
section
noncomputable section

namespace Formalism.BasicNotions.Examples₂

open NumberField IsDedekindDomain Formalism.MainNotions.S

def FdegUniq (R : Ranks) (h : HCParam R) : Prop :=
  ∃ d0 : ℝ, 0 < d0 ∧ ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (σ : Matrix (Fin (2 * R.rS + R.k + 1)) (Fin (2 * R.rS + R.k + 1)) ℂ → (V →L[ℂ] V)) (d : ℝ),
    IsDS (epsSH R) (lamSH R h) σ →
    IsFdeg ((CD.cdScaleOf CD.cdHaar _ (epsSH R) : ENNReal) • Formalism.REAL.muG (epsSH R)) σ d → d = d0

variable {R : Ranks} (H : Host R)

variable (hc : Tau2 R → HCParam R) (Del : ℚ) (hDel : 0 < Del)
  (hgap : ∀ (τ : Tau2 R) (l : ℕ) (h : l + 1 < R.k - 1),
    (hc τ).v ⟨l, by omega⟩ - (hc τ).v ⟨l + 1, h⟩ = 4 * Del)
  (hlet : ∀ (τ : Tau2 R) (l : ℕ) (h : l < R.k - 2),
    (hc τ).u ⟨l + 1, by omega⟩ = (hc τ).v ⟨l, by omega⟩ - 1 / 2)
  (cdS : ∀ (n : ℕ) (_ : Fin n → Bool), NNReal) (hcdS : ∀ n ε, 0 < cdS n ε)
  (dsg : Tau2 R → ℝ) (hdsg : ∀ ρ, 0 < dsg ρ) (etaF : ℝ)

variable (T : ℕ) [hT : Fact T.Prime] (Ts : ℝ) (hTs : 0 < Ts) (Gam : ℝ) (hG : 1 < Gam)
  (hw1 : Ts ≤ T) (hw2 : (T : ℝ) ≤ (1 + 1 / ((R.f : ℝ) * R.k)) * Ts)
  (hg : ∀ k, (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E) (ht : THyp H)
  (hlev : T ∈ H.levelPrimes) (hpde : T ≠ H.pde ∧ T ≠ H.pde')
  (pz : 𝓞 H.E) (hK : (pz : H.E) ∈ H.K) (hpz : (pz : H.E) * H.conj (pz : H.E) = (T : H.E))
  (hcong : (pz - 1) ∈ Ideal.span {((H.QS * H.q * H.d * (H.g 0 * H.g 1) ^ 2 : ℕ) : 𝓞 H.E)})
  (G : LocalGap H)

abbrev normalisedGenericRecord (hu : ∀ τ, FdegUniq R (hc τ)) : D7 :=
  rankRecord H hc Del hDel hgap hlet (CD.cdScaleOf CD.cdHaar) (CD.cdScaleOf_pos _)
      (fun τ => (hu τ).choose) (fun τ => (hu τ).choose_spec.1) etaF T Ts hTs Gam hG hw1 hw2 hg ht hlev hpde pz hK hpz hcong G

def d7Tw (hu : ∀ τ, FdegUniq R (hc τ))
    (C : @TwCore R H (normalisedGenericRecord H hc Del hDel hgap hlet etaF T Ts hTs Gam hG hw1 hw2 hg ht hlev hpde pz hK hpz hcong G hu).what₂ (inferInstanceAs (NumberField H.E)) H.cmStar
      (normalisedGenericRecord H hc Del hDel hgap hlet etaF T Ts hTs Gam hG hw1 hw2 hg ht hlev hpde pz hK hpz hcong G hu).LL0 (normalisedGenericRecord H hc Del hDel hgap hlet etaF T Ts hTs Gam hG hw1 hw2 hg ht hlev hpde pz hK hpz hcong G hu).nd) : D7 :=
  withTw (normalisedGenericRecord H hc Del hDel hgap hlet etaF T Ts hTs Gam hG hw1 hw2 hg ht hlev hpde pz hK hpz hcong G hu) (TwCore.toGap _ ⟨fun i => Empty.elim i⟩
    (fun g => newtypes_idempotent_zero H _ _ ht G.tame g) C)

theorem ties_d7Tw (hu C) : Ties (d7Tw H hc Del hDel hgap hlet etaF T Ts hTs Gam hG hw1 hw2 hg ht hlev hpde pz hK hpz hcong G hu C) :=
  ties_withTw _ _ rfl (fun τ V _ _ σ d h1 h2 => (hu τ).choose_spec.2 V σ d h1 h2)
    (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)
    ⟨fun σ => Empty.elim σ⟩

end Formalism.BasicNotions.Examples₂
end
end

