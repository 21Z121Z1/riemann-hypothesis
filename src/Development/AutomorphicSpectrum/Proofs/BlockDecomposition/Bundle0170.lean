import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CombinatorialCechAcyclic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapConeRing
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0139
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0140
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0141
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0138
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0158
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0164
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0151
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0146
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0134
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MemBoundariesZeroIff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0135
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0145
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0162
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0167
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalisationLadders.CriterionTruncation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0166
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.BasisB
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedSplittingOverLatticeBase

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrystallineFiltrationSpanDividedPowers
section
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.PerfFil

variable {l : ℕ} [Fact l.Prime] (A : PAlg l)

theorem divided_power_xi_zero : A.dxi0 0 = 1 :=
  Subtype.ext (by simp [PAlg.dxi0, dpw])

theorem divided_power_xi_mul (i j : ℕ) :
    A.dxi0 i * A.dxi0 j = (((i + j).choose i : ℕ) : A.Acr0) * A.dxi0 (i + j) := by
  apply Subtype.ext
  have hi := A.isUnit_natCast (Nat.factorial_ne_zero i)
  have hj := A.isUnit_natCast (Nat.factorial_ne_zero j)
  have hij := A.isUnit_natCast (Nat.factorial_ne_zero (i + j))
  change dpw i A.xi * dpw j A.xi = (((i + j).choose i : ℕ) : WL l A.A) * dpw (i + j) A.xi
  simp only [dpw]
  apply hij.mul_left_cancel
  have hc : (((i + j).factorial : ℕ) : WL l A.A) =
      (((i + j).choose i : ℕ) : WL l A.A) * ((i.factorial : ℕ) : WL l A.A) * ((j.factorial : ℕ) : WL l A.A) := by
    have := Nat.add_choose_mul_factorial_mul_factorial i j
    rw [← Nat.choose_symm_add] at this
    rw [← Nat.cast_mul, ← Nat.cast_mul, this]
  calc _ = (((i + j).choose i : ℕ) : WL l A.A) * (((i.factorial : ℕ) : WL l A.A) * Ring.inverse ((i.factorial : ℕ) : WL l A.A))
        * (((j.factorial : ℕ) : WL l A.A) * Ring.inverse ((j.factorial : ℕ) : WL l A.A))
        * (algebraMap _ (WL l A.A) A.xi ^ i * algebraMap _ (WL l A.A) A.xi ^ j) := by
          rw [hc]; ring
    _ = (((i + j).choose i : ℕ) : WL l A.A) * (algebraMap _ (WL l A.A) A.xi ^ (i + j)) := by
          rw [Ring.mul_inverse_cancel _ hi, Ring.mul_inverse_cancel _ hj, pow_add]; ring
    _ = _ := by
          rw [mul_left_comm, ← mul_assoc (((i + j).factorial : ℕ) : WL l A.A), Ring.mul_inverse_cancel _ hij, one_mul]

def spanFrom (r : ℕ) : Submodule A.W A.Acr0 :=
  Submodule.span A.W {z : A.Acr0 | ∃ k, r ≤ k ∧ z = A.dxi0 k}

theorem divided_power_xi_mem_span_from {r k : ℕ} (h : r ≤ k) : A.dxi0 k ∈ spanFrom A r :=
  Submodule.subset_span ⟨k, h, rfl⟩

theorem natCast_mul_mem (r : ℕ) (n : ℕ) {z : A.Acr0} (hz : z ∈ spanFrom A r) :
    (n : A.Acr0) * z ∈ spanFrom A r := by
  rw [← nsmul_eq_mul]
  exact (spanFrom A r).toAddSubmonoid.nsmul_mem hz n

theorem mul_mem_spanFrom (r : ℕ) {a b : A.Acr0} (ha : a ∈ spanFrom A 0) (hb : b ∈ spanFrom A r) :
    a * b ∈ spanFrom A r := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, -, rfl⟩ := hx
    induction hb using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, hj, rfl⟩ := hy
      rw [divided_power_xi_mul]
      exact natCast_mul_mem A r _ (divided_power_xi_mem_span_from A (by omega))
    | zero => rw [mul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
    | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hx
  | zero => rw [zero_mul]; exact zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx

theorem mem_spanFrom_zero (z : A.Acr0) : z ∈ spanFrom A 0 := by
  obtain ⟨y, hy⟩ := z
  induction hy using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨k, rfl⟩ := hy
    exact divided_power_xi_mem_span_from A (Nat.zero_le k)
  | algebraMap x =>
    have h := Submodule.smul_mem (spanFrom A 0) x (divided_power_xi_mem_span_from A (le_refl 0))
    rw [divided_power_xi_zero] at h
    convert h using 1
    exact Subtype.ext (by simp [Algebra.smul_def])
  | add x y hx' hy' hx hy => exact add_mem hx hy
  | mul x y hx' hy' hx hy => exact mul_mem_spanFrom A 0 hx hy

theorem mem_crystalline_filtration_iff_span {l : ℕ} [Fact l.Prime] (A : PAlg l) (r : ℕ) (z : A.Acr0) :
    z ∈ A.Fil0 r ↔ z ∈ Submodule.span A.W {z : A.Acr0 | ∃ k, r ≤ k ∧ z = A.dxi0 k} := by
  constructor
  · intro h
    induction h using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span hx
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul c x _ hx => exact mul_mem_spanFrom A r (mem_spanFrom_zero A c) hx
  · intro h
    induction h using Submodule.span_induction with
    | mem x hx => exact Ideal.subset_span hx
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul c x _ hx =>
      rw [Algebra.smul_def]
      exact Ideal.mul_mem_left _ _ hx

end GlobalTheory.CompanionTheory.PerfFil
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsTheta
section
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.SurjectionOntoH4
open CrystallineSemistableComparison.Onto

variable {K : Type} [Field K] {n d : ℕ}

theorem exists_theta {A : Type} [CommRing A] [Algebra K A] (C : ChartRings K A n d) :
    ∃ (θ : ∀ S, R0 K n d S →ₐ[K] C.R S) (hθ : ∀ S b, θ S (poly n K S b) = toR C S (phi C b)),
      (∀ {S T : Finset (Fin d)} (h : S ⊆ T) y, C.res h (θ S y) = θ T (incl (cone_mono h) y)) ∧
      ∀ S, IsBaseChange (Aa C) (thetaLin C (θ S) (hθ S)) := by
  have key : ∀ S, ∃ (θ : R0 K n d S →ₐ[K] C.R S) (hθ : ∀ b, θ (poly n K S b) = toR C S (phi C b)),
      IsBaseChange (Aa C) (thetaLin C θ hθ) := by
    intro S
    rcases S.eq_empty_or_nonempty with rfl | ⟨k, hk⟩
    · exact GlobalTheory.T.chart_empty_base_change C
    · obtain ⟨θ₁, h₁, hu, hb⟩ := GlobalTheory.T.chart_singleton_base_change C k
      exact GlobalTheory.T.chart_extend_base_change C S k hk θ₁ h₁ hu hb
  choose θ hθ bc using key
  refine ⟨θ, hθ, ?_, bc⟩
  intro S T h y
  have := GlobalTheory.T.chart_base_change_map_unique C ((C.res h).comp (θ S)) ((θ T).comp (incl (cone_mono h)))
    (fun b => by rw [AlgHom.comp_apply, hθ, res_toR]) (fun b => by rw [AlgHom.comp_apply, incl_poly h, hθ]) (θ T) (hθ T) (bc T)
  exact DFunLike.congr_fun this y

theorem Tset_ne_univ (g : Gam n d) (D : Finset (E n d)) (h : good g D) : Tset g D ≠ Finset.univ := by
  intro hu
  have hneg : ∀ j, g (Sum.inr j) ≤ 0 := fun j => by
    have : j ∈ Tset g D := hu ▸ Finset.mem_univ j
    rcases (Finset.mem_filter.1 this).2 with h | h
    · exact h.le
    · exact h.1.le
  have : tdeg g ≤ 0 := Finset.sum_nonpos fun j _ => hneg j
  have := h.2
  omega

theorem model_ex (a : ℕ) : ExP (fun S : Finset (Fin d) => relOm K (I0 n K S) a)
    (fun {S T} h => relMap (incl (cone_mono h)) (cone_ideal_map_mono (S := S) (T := T) h) a) := by
  obtain ⟨b, hb⟩ := GlobalTheory.T.monomial_forms_basis (K := K) (n := n) (d := d) a
  refine GlobalTheory.T.finset_system_injective_extension (K := K) b (fun p => good p.1 p.2.1) (fun p => Tset p.1 p.2.1) (fun p h => Tset_ne_univ _ _ h) _ _
    (fun S => ((omMap (K := K) (incl (le_top : (cone S : AddSubmonoid (Gam n d)) ≤ ⊤)) a).toAddMonoidHom).comp
      (relOm K (I0 n K S) a).subtype.toAddMonoidHom) ?_ ?_ ?_
  · intro S x y hxy
    exact Subtype.ext (GlobalTheory.T.cone_forms_map_injective S a hxy)
  · intro S S' h x
    change omMap _ a (omMap _ a (x : Om K (R0 K n d S) a)) = omMap _ a (x : Om K (R0 K n d S) a)
    rw [omMap_comp, incl_comp]
  · intro S w
    have hset : (b '' {l | good l.1 l.2.1 ∧ Tset l.1 l.2.1 ⊆ S}) =
        {w | ∃ (g : Gam n d) (D : {D : Finset (E n d) // D.card = a}), good g D.1 ∧ Tset g D.1 ⊆ S ∧ w = monW K g D} := by
      ext w
      constructor
      · rintro ⟨p, hp, rfl⟩
        exact ⟨p.1, p.2, hp.1, hp.2, hb p⟩
      · rintro ⟨g, D, h1, h2, rfl⟩
        exact ⟨(g, D), ⟨h1, h2⟩, hb _⟩
    rw [hset]
    constructor
    · rintro ⟨x, rfl⟩
      exact GlobalTheory.T.relative_forms_map_mem_span S a _ x.2
    · intro hw
      induction hw using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨g, D, h1, h2, rfl⟩ := hw
        obtain ⟨ω, hω, e⟩ := GlobalTheory.T.monomial_form_in_relative_image (K := K) S a g D h1 h2
        exact ⟨⟨ω, hω⟩, e⟩
      | zero => exact ⟨0, by simp⟩
      | add x y _ _ hx hy =>
        obtain ⟨x', rfl⟩ := hx
        obtain ⟨y', rfl⟩ := hy
        exact ⟨x' + y', map_add _ _ _⟩
      | smul c x _ hx =>
        obtain ⟨x', rfl⟩ := hx
        exact ⟨c • x', map_smul (omMap (K := K) (incl (le_top : (cone S : AddSubmonoid (Gam n d)) ≤ ⊤)) a) c _⟩

theorem h4a : ChartFormsCechExact := by
  intro K _ _ A _ _ n d hd C a P e he
  obtain ⟨θ, hθ, nat, bc⟩ := exists_theta C
  haveI := etale_Aa C
  have h1 := model_ex (K := K) (n := n) (d := d) a
  have h2 : ExP (fun S => relA C S a) (fun {S T} h => relMap (C.res h) (res_mem_I C (S := S) (T := T) h) a) := by
    refine GlobalTheory.T.finset_system_scalar_tower_ext (B := Bp K n d) (A := Aa C) (fun S => relOm K (I0 n K S) a) (fun S => relA C S a) _ ?_ _ ?_
      (fun S => psi C (θ S) (hθ S) a) (fun S => GlobalTheory.T.chart_forms_base_change C (θ S) (hθ S) (bc S) a) ?_ h1
    · intro S T h
      refine ⟨map_add _, fun b ω => Subtype.ext ?_⟩
      change omMap (incl (cone_mono h)) a ((b • ω : relOm K (I0 n K S) a) : Om K (R0 K n d S) a) =
        ((b • relMap (incl (cone_mono h)) (cone_ideal_map_mono h) a ω : relOm K (I0 n K T) a) : Om K (R0 K n d T) a)
      have e1 : ∀ (U : Finset (Fin d)) (ω' : relOm K (I0 n K U) a), ((b • ω' : relOm K (I0 n K U) a) : Om K (R0 K n d U) a) =
          poly n K U b • (ω' : Om K (R0 K n d U) a) := fun U ω' =>
        (algebraMap_smul (R0 K n d U) b (ω' : Om K (R0 K n d U) a)).symm
      rw [e1, e1, omMap_smul, incl_poly h]
      rfl
    · intro S T h
      refine ⟨map_add _, fun c y => Subtype.ext ?_⟩
      change omMap (C.res h) a (toR C S c • (y : relOm K (C.I S) a).1) = toR C T c • omMap (C.res h) a (y : relOm K (C.I S) a).1
      rw [omMap_smul]
      exact congrArg (· • omMap (C.res h) a (y : relOm K (C.I S) a).1) (res_toR C h c)
    · intro S T h ω
      refine Subtype.ext ?_
      change omMap (C.res h) a (omMap (θ S) a (ω : Om K (R0 K n d S) a)) =
        omMap (θ T) a (omMap (incl (cone_mono h)) a (ω : Om K (R0 K n d S) a))
      have e2 : (C.res h).comp (θ S) = (θ T).comp (incl (cone_mono h)) := AlgHom.ext fun y => nat h y
      rw [omMap_comp, omMap_comp, e2]
  refine GlobalTheory.T.pm_exactness_of_exP P (GlobalTheory.T.exP_of_compatible_equiv _ _ (fun {S T} h => relMap (C.res h) (res_mem_I C (S := S) (T := T) h) a) _
    (fun S => ((e S).symm.toAddEquiv : relA C S a ≃+ P.M S)) ?_ h2)
  intro S T h x
  apply (e T).injective
  refine Subtype.ext ?_
  have := he h ((e S).symm x)
  simp only [LinearEquiv.apply_symm_apply] at this
  have h3 := LinearEquiv.apply_symm_apply (e T) (relMap (C.res h) (res_mem_I C h) a x)
  exact (congrArg Subtype.val h3).trans this.symm

end GlobalTheory.CompanionTheory.SurjectionOntoH4
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatBaseChangeCohomology
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section

universe w v u w' v' u'

namespace GlobalTheory.CompanionTheory.CosieveBC

open GlobalTheory.CompanionTheory.CosieveMV

section Cover

variable {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {C : Type u} [Category.{v} C]
  {C' : Type u'} [Category.{v'} C'] {G : C' ⥤ C} {ι : Type} {N : ι → Type} [∀ i, AddCommGroup (N i)]
  [∀ i, Module R (N i)] {F : ι → (C ⥤ ModuleCat.{w} R)} {F' : C' ⥤ ModuleCat.{w'} R'}
  {τ : ∀ i, N i → ∀ T : C', (F i).obj (G.obj T) →ₛₗ[σ] F'.obj T}
  {hτ : ∀ i n {T T' : C'} (φ : T ⟶ T') x, τ i n T' (((F i).map (G.map φ)).hom x) = (F'.map φ).hom (τ i n T x)}

theorem subsingleton_H {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{w} R)
    {W : ObjectProperty C} (h : ∀ T, ¬ W T) (j : ℕ) : Subsingleton ((cw F W).H j) := by
  have : Subsingleton ((cw F W).X j) := ⟨fun _ _ => funext fun s => (h _ (s.obj 0).property).elim⟩
  refine subsingleton_of_forall_eq 0 fun x => ?_
  obtain ⟨a, ha, rfl⟩ := CrystallineSemistableComparison.CechClassBoundaries.clsSurj x
  refine (CrystallineSemistableComparison.CechClassBoundaries.cls_eq_zero a ha).2 ?_
  rw [Subsingleton.elim a 0]
  exact zero_mem _

theorem bc_congr [DecidableEq ι] {W W₂ : ObjectProperty C} {W' W₂' : ObjectProperty C'} (e : ∀ T, W T ↔ W₂ T)
    (e' : ∀ T, W' T ↔ W₂' T) (h : ∀ T, W' T → W (G.obj T)) (h₂ : ∀ T, W₂' T → W₂ (G.obj T))
    (t : BC (Phi G F F' τ hτ h)) : BC (Phi G F F' τ hτ h₂) := by
  obtain rfl : W = W₂ := funext fun T => propext (e T)
  obtain rfl : W' = W₂' := funext fun T => propext (e' T)
  exact t

theorem Wc_insert {α : Type} [DecidableEq α] {D : Type u} [Category.{v} D] (U : α → ObjectProperty D) (a : α)
    (A S : Finset α) (T : D) : supP (Wc U A S) (capS U (insert a S)) T ↔ Wc U (insert a A) S T := by
  constructor
  · rintro (⟨⟨b, hb, hT⟩, hS⟩ | h)
    · exact ⟨⟨b, Finset.mem_insert_of_mem hb, hT⟩, hS⟩
    · exact ⟨⟨a, Finset.mem_insert_self _ _, h a (Finset.mem_insert_self _ _)⟩,
        fun b hb => h b (Finset.mem_insert_of_mem hb)⟩
  · rintro ⟨⟨b, hb, hT⟩, hS⟩
    rcases Finset.mem_insert.1 hb with rfl | h
    · refine Or.inr fun c hc => ?_
      rcases Finset.mem_insert.1 hc with rfl | h'
      · exact hT
      · exact hS c h'
    · exact Or.inl ⟨⟨b, h, hT⟩, hS⟩

theorem Wc_inf {α : Type} [DecidableEq α] {D : Type u} [Category.{v} D] (U : α → ObjectProperty D) (a : α)
    (A S : Finset α) (T : D) : Wc U A (insert a S) T ↔ infP (Wc U A S) (capS U (insert a S)) T :=
  ⟨fun h => ⟨⟨h.1, fun b hb => h.2 b (Finset.mem_insert_of_mem hb)⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩

theorem wc_le {α : Type} {U : α → ObjectProperty C} {U' : α → ObjectProperty C'}
    (h : ∀ a T, U' a T → U a (G.obj T)) (A S : Finset α) (T : C') (hT : Wc U' A S T) : Wc U A S (G.obj T) := by
  obtain ⟨⟨a, ha, hT⟩, hS⟩ := hT
  exact ⟨⟨a, ha, h a T hT⟩, fun b hb => h b T (hS b hb)⟩

theorem cap_le {α : Type} {U : α → ObjectProperty C} {U' : α → ObjectProperty C'}
    (h : ∀ a T, U' a T → U a (G.obj T)) (S : Finset α) (T : C') (hT : capS U' S T) : capS U S (G.obj T) :=
  fun b hb => h b T (hT b hb)

theorem bc_Wc [Fintype ι] [DecidableEq ι] [∀ i, Module.Flat R (N i)] {α : Type} [DecidableEq α]
    (hadd : ∀ i n n' T x, τ i (n + n') T x = τ i n T x + τ i n' T x)
    (hsm : ∀ i (r : R) n T x, τ i (r • n) T x = σ r • τ i n T x)
    {U : α → ObjectProperty C} {U' : α → ObjectProperty C'} (hU : ∀ a, Cosieve (U a)) (hU' : ∀ a, Cosieve (U' a))
    (h : ∀ a T, U' a T → U a (G.obj T))
    (hcap : ∀ S : Finset α, S.Nonempty → BC (Phi G F F' τ hτ (cap_le h S))) (A : Finset α) :
    ∀ S : Finset α, BC (Phi G F F' τ hτ (wc_le h A S)) := by
  induction A using Finset.induction_on with
  | empty =>
    intro S j
    have e : ∀ {D : Type u} [Category.{v} D] (P : α → ObjectProperty D) (T : D), ¬ Wc P ∅ S T := by
      intro D _ P T hT
      simpa using hT.1
    have e' : ∀ {D : Type u'} [Category.{v'} D] (P : α → ObjectProperty D) (T : D), ¬ Wc P ∅ S T := by
      intro D _ P T hT
      simpa using hT.1
    have s1 := fun i => subsingleton_H (F i) (e U) j
    have s2 := subsingleton_H F' (e' U') j
    exact tens_subsingleton _
  | insert a A ha ih =>
    intro S
    have key := bc_sup (G := G) (F := F) (F' := F') (τ := τ) (hτ := hτ) hadd hsm (cosieve_Wc hU A S)
      (cosieve_capS hU (insert a S)) (cosieve_Wc hU' A S) (cosieve_capS hU' (insert a S))
      (wc_le h A S) (cap_le h (insert a S)) (ih S) (hcap _ (Finset.insert_nonempty _ _))
      (bc_congr (Wc_inf U a A S) (Wc_inf U' a A S) _ _ (ih (insert a S)))
    exact bc_congr (Wc_insert U a A S) (Wc_insert U' a A S) _ _ key

theorem restrict_bij {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{w} R)
    {W : ObjectProperty C} (hall : ∀ T, W T) (n : ℕ) :
    Function.Bijective ((CH.Mor.restrict F W.ι).hom.f n) := by
  have hW : Cosieve W := fun _ _ _ _ => hall _
  refine ⟨fun x y hxy => funext fun s => congrFun hxy (liftCh hW s (hall _)), fun y => ⟨extZ hW y, pull_extZ hW y⟩⟩

def resEquiv {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{w} R)
    {W : ObjectProperty C} (hall : ∀ T, W T) (j : ℕ) : CH.H F j ≃ₗ[R] (cw F W).H j :=
  LinearEquiv.ofBijective ((CH.Mor.restrict F W.ι).hom.mapH j) (CrystallineSemistableComparison.P.mapH_bij _ (restrict_bij F hall) j)

theorem tens_top [Fintype ι] [DecidableEq ι]
    (hadd : ∀ i n n' T x, τ i (n + n') T x = τ i n T x + τ i n' T x)
    (hsm : ∀ i (r : R) n T x, τ i (r • n) T x = σ r • τ i n T x)
    {W : ObjectProperty C} {W' : ObjectProperty C'} (hall : ∀ T, W T) (hall' : ∀ T, W' T)
    (h : ∀ T, W' T → W (G.obj T)) (t : BC (Phi G F F' τ hτ h)) (j : ℕ) :
    Tens R (N := N) (M := fun i => CH.H (F i) j) (M' := CH.H F' j)
      fun i n x => (⟨G, τ i n, hτ i n⟩ : CH.Mor (F i) F' σ).pull j x := by
  have lq : Lin (K := fun i => CH.cx (F i)) (K' := CH.cx F') (σ := σ)
      fun i n => (⟨G, τ i n, hτ i n⟩ : CH.Mor (F i) F' σ).hom :=
    ⟨fun i n n' k x => funext fun s => hadd i n n' _ _, fun i r n k x => funext fun s => hsm i r n _ _⟩
  refine tens_of_bij (bal_mapH (phi_lin hadd hsm h) j) (bal_mapH lq j) (fun i => resEquiv (F i) hall j)
    (resEquiv F' hall' j).toAddEquiv (fun i n x => ?_) (t j)
  obtain ⟨a, ha, rfl⟩ := CrystallineSemistableComparison.CechClassBoundaries.clsSurj x
  rfl

end Cover

theorem base_change_of_cover : ∀ {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {C C' : Type 1} [Category.{0} C] [Category.{0} C']
    (G : C' ⥤ C) {ι : Type} [Fintype ι] [DecidableEq ι] (N : ι → Type) [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
    [∀ i, Module.Flat R (N i)] (F : ι → (C ⥤ ModuleCat.{0} R)) (F' : C' ⥤ ModuleCat.{0} R')
    (τ : ∀ i, N i → ∀ T : C', (F i).obj (G.obj T) →ₛₗ[σ] F'.obj T) (hτ : ∀ i n {T T' : C'} (φ : T ⟶ T') x,
      τ i n T' (((F i).map (G.map φ)).hom x) = (F'.map φ).hom (τ i n T x))
    (hadd : ∀ i n n' T x, τ i (n + n') T x = τ i n T x + τ i n' T x) (hsm : ∀ i (r : R) n T x, τ i (r • n) T x = σ r • τ i n T x)
    {A : Type} [Fintype A] (U : A → ObjectProperty C) (U' : A → ObjectProperty C') (hU : ∀ α, Cosieve (U α))
    (hU' : ∀ α, Cosieve (U' α)) (hc : ∀ T, ∃ α, U α T) (hc' : ∀ T, ∃ α, U' α T) (h : ∀ α T, U' α T → U α (G.obj T)),
    (∀ S : Finset A, S.Nonempty → ∀ j, Tens R (N := N) (M := fun i => HU (F i) (capS U S) j) (M' := HU F' (capS U' S) j)
      fun i n x => (morU (⟨G, τ i n, hτ i n⟩ : CH.Mor (F i) F' σ) (U := capS U S) (U' := capS U' S)
        fun T hT α hα => h α T (hT α hα)).pull j x) →
    ∀ j, Tens R (N := N) (M := fun i => CH.H (F i) j) (M' := CH.H F' j)
      fun i n x => (⟨G, τ i n, hτ i n⟩ : CH.Mor (F i) F' σ).pull j x := by
  intro R R' _ _ σ C C' _ _ G ι _ _ N _ _ _ F F' τ hτ hadd hsm A _ U U' hU hU' hc hc' h H j
  classical
  have key := bc_Wc (G := G) (F := F) (F' := F') (τ := τ) (hτ := hτ) hadd hsm hU hU' h
    (fun S hS j => H S hS j) Finset.univ ∅
  refine tens_top hadd hsm (W := Wc U Finset.univ ∅) (W' := Wc U' Finset.univ ∅) (fun T => ?_) (fun T => ?_) _ key j
  · obtain ⟨a, ha⟩ := hc T
    exact ⟨⟨a, Finset.mem_univ _, ha⟩, fun b hb => by simp at hb⟩
  · obtain ⟨a, ha⟩ := hc' T
    exact ⟨⟨a, Finset.mem_univ _, ha⟩, fun b hb => by simp at hb⟩

end GlobalTheory.CompanionTheory.CosieveBC
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameFormRespectsFiltration
section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.FormMem

theorem prod_fil_mem {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {Fil : ℤ → IdF Φ.A}
    (hF : IsFil Φ Fil) (T : C) : ∀ (n : ℕ) (f : Fin n → Φ.A.obj T), (∀ k, f k ∈ (Fil 1).S T) →
      ∏ k, f k ∈ (Fil (n : ℤ)).S T
  | 0, f, _ => by
    have h : (Fil ((0 : ℕ) : ℤ)).S T = ⊤ := hF.top _ (by simp) T
    rw [h]
    exact Submodule.mem_top
  | n + 1, f, h => by
    rw [Fin.prod_univ_succ]
    have h0 : f 0 ∈ (Fil ((1 : ℕ) : ℤ)).S T := by simpa using h 0
    have := hF.mul 1 n T h0 (prod_fil_mem hF T n (fun k => f k.succ) fun k => h k.succ)
    rwa [Nat.add_comm] at this

theorem form_mem : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil)
    {d : ℕ} (E : Frame Φ d) (σ : ∀ T : C, E.D ⟶ T) (j q : ℕ) (I : Fin j → Fin d) (x : Φ.A.obj E.D), x ∈ (Fil q).S E.D →
    ∀ s : ComposableArrows C j, E.form σ I x s ∈ (Fil ((j + q : ℕ) : ℤ)).S (s.obj (Fin.last j)) := by
  intro R _ C _ Φ Fil hF d E σ j q I x hx s
  refine hF.mul j q _ (prod_fil_mem hF _ j _ fun k => (Fil 1).map_mem _ ?_) ((Fil q).map_mem (σ _) hx)
  rw [hF.one]
  exact E.mem _ _ _

end GlobalTheory.CompanionTheory.FormMem
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctorialityOfPeriodRingMaps
section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.PAlgNat

variable {l : ℕ} [Fact l.Prime]

theorem mapAcris_acrisOfTilt {A B : PAlg l} (f : A ⟶ B) (a : A.A) :
    mapAcr f 1 (A.aTo1 a) = B.aTo1 (Hom.f f a) := by
  have h := A.aTo1_coeff (WittVector.teichmuller l a)
  rw [WittVector.teichmuller_coeff_zero] at h
  have h' := B.aTo1_coeff (WittVector.teichmuller l (Hom.f f a))
  rw [WittVector.teichmuller_coeff_zero] at h'
  rw [h, h', mapAcr_toAcr, mapW, WittVector.map_teichmuller]

theorem mapAcr_expand {A B : PAlg l} (f : A ⟶ B) (c : ℕ →₀ A.A) :
    mapAcr f 1 (A.expand c) = B.expand (c.mapRange (Hom.f f) (map_zero _)) := by
  rw [expand, expand, map_finsuppSum, Finsupp.sum_mapRange_index (fun k => by simp)]
  refine Finsupp.sum_congr fun k _ => ?_
  rw [map_mul, mapAcris_acrisOfTilt, mapAcr_dxi]

theorem mapU_sharp {A B : PAlg l} (f : A ⟶ B) (a : A.A) :
    mapU f (A.sharp a) = B.sharp (Hom.f f a) := by
  change mapU f (A.th (WittVector.teichmuller l a)) = B.th (WittVector.teichmuller l (Hom.f f a))
  rw [mapU_th, mapW, WittVector.map_teichmuller]

theorem mapUnits_unitsOfTilt {A B : PAlg l} (f : A ⟶ B) (a : A.A) :
    mapUn f 1 (A.aToU1 a) = B.aToU1 (Hom.f f a) := by
  rw [sharpMap_eq, sharpMap_eq, ← mapU_sharp]
  rfl

theorem mk_mapAcr_toAcr {A B : PAlg l} (f : A ⟶ B) (n : ℕ) (x : A.W) :
    Ideal.Quotient.mk (B.Fil n 1) (mapAcr f n (A.toAcr n x)) = B.uToQ n (mapU f (A.th x)) := by
  rw [mapAcr_toAcr, mapU_th, uToQ_th]

theorem algebraMap_eq_acrisOfTilt (A : PAlg l) (x : Ainf l) :
    algebraMap (Ainf l) (A.Acr 1) x = A.aTo1 (A.s (x.coeff 0)) := by
  have h := A.aTo1_coeff (A.sW x)
  have e : (A.sW x).coeff 0 = A.s (x.coeff 0) := WittVector.map_coeff _ _ _
  rw [e] at h
  rw [h]
  rfl

theorem expand_nat {l : ℕ} [Fact l.Prime] (A : PAlg l) (B : PAlg l) (f : A ⟶ B) :
    (∀ a, mapAcr f 1 (A.aTo1 a) = B.aTo1 (Hom.f f a)) ∧
    (∀ c : ℕ →₀ A.A, mapAcr f 1 (A.expand c) = B.expand (c.mapRange (Hom.f f) (map_zero _))) ∧
    (∀ a, mapU f (A.sharp a) = B.sharp (Hom.f f a)) ∧
    (∀ a, mapUn f 1 (A.aToU1 a) = B.aToU1 (Hom.f f a)) ∧
    (∀ n x, Ideal.Quotient.mk (B.Fil n 1) (mapAcr f n (A.toAcr n x)) = B.uToQ n (mapU f (A.th x))) ∧
    ∀ x : Ainf l, algebraMap (Ainf l) (A.Acr 1) x = A.aTo1 (A.s (x.coeff 0)) :=
  ⟨mapAcris_acrisOfTilt f, mapAcr_expand f, mapU_sharp f, mapUnits_unitsOfTilt f, mk_mapAcr_toAcr f, algebraMap_eq_acrisOfTilt A⟩

end GlobalTheory.CompanionTheory.PAlgNat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedSplittingOverFieldStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graded_splitting_over_field : ∀ {K B : Type} [Field K] [CommRing B] [Algebra K B] {I : Ideal B} (γ : DividedPowers I) (m : ℕ),
    pdP γ m = ⊥ → Nonempty (GrSplit K γ m) := by
  first | exact @GlobalTheory.CompanionTheory.GrSplitField.nonempty_grSplit | exact GlobalTheory.CompanionTheory.GrSplitField.nonempty_grSplit | (intros; apply GlobalTheory.CompanionTheory.GrSplitField.nonempty_grSplit <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedSplittingOverLatticeBaseStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graded_splitting_over_lattice_base : ∀ {O A : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing A] [Algebra O A] {I : Ideal A}
    (γ : DividedPowers I) (l m : ℕ), (∀ a : O, a ≠ 0 → ∃ k : ℕ, a ∣ (l : O) ^ k) → LatBase γ l m → Nonempty (GrSplit O γ m) := by
  first | exact @GlobalTheory.CompanionTheory.LatSplit.nonempty_grSplit | exact GlobalTheory.CompanionTheory.LatSplit.nonempty_grSplit | (intros; apply GlobalTheory.CompanionTheory.LatSplit.nonempty_grSplit <;> assumption)
end

