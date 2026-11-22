import ReciprocityTheory.GroupCohomology.Bundle0002
import ReciprocityTheory.GroupCohomology.Bundle0003
import ReciprocityTheory.GroupCohomology.ConnNatHolds
import ReciprocityTheory.GroupCohomology.Bundle0004
import ReciprocityTheory.GroupCohomology.PrismOpZeroEval
import ReciprocityTheory.GroupCohomology.Bundle0005

-- bundled from ReciprocityTheory.GroupCohomology.FiberFirstH0Injective
section
namespace ReciprocityTheory.Coh
open Cx Function
noncomputable section
universe u

namespace ProjectiveLinePlaces
variable {R : Type u} [CommRing R] {A B : Cx R}

theorem cls_eq_zero (A : Cx R) (n : ℕ) (x : A.X n) (hx) : A.cls n x hx = 0 ↔ x ∈ A.B n := by
  unfold Cx.cls; rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]; rfl

theorem mem_B_zero (A : Cx R) (x : A.X 0) : x ∈ A.B 0 ↔ x = 0 := Submodule.mem_bot R
theorem mem_B_succ (A : Cx R) (n : ℕ) (x : A.X (n+1)) : x ∈ A.B (n+1) ↔ ∃ y, A.d n y = x :=
  LinearMap.mem_range

theorem H_cls (φ : Hom A B) (n : ℕ) (x : A.X n) (hx) :
    φ.H n (A.cls n x hx) = B.cls n (φ.f n x) (by rw [← φ.comm, hx, map_zero]) := rfl

theorem fib_d_snd_zero (φ : Hom A B) (x : (fib φ).X 0) : (((fib φ).d 0 x).2 : B.X 0) = φ.f 0 x.1 := by
  have h : (show B.X 0 from B.up.d 0 x.2) = 0 := rfl
  show φ.f 0 x.1 + (show B.X 0 from B.up.d 0 x.2) = _
  rw [h, add_zero]

theorem fib_d_snd_succ (φ : Hom A B) (n : ℕ) (x : (fib φ).X (n+1)) :
    (((fib φ).d (n+1) x).2 : B.X (n+1)) = φ.f (n+1) x.1 - B.d n x.2 := by
  show φ.f (n+1) x.1 + -B.d n x.2 = _
  rw [sub_eq_add_neg]

theorem fib_d_succ_iff (φ : Hom A B) (n : ℕ) (x : (fib φ).X (n+1)) :
    (fib φ).d (n+1) x = 0 ↔ A.d (n+1) x.1 = 0 ∧ φ.f (n+1) x.1 = B.d n x.2 := by
  constructor
  · intro h; exact ⟨congrArg Prod.fst h, sub_eq_zero.mp ((fib_d_snd_succ φ n x).symm.trans (congrArg Prod.snd h))⟩
  · rintro ⟨h1, h2⟩; exact Prod.ext h1 ((fib_d_snd_succ φ n x).trans (sub_eq_zero.mpr h2))

theorem cls_congr (A : Cx R) (n : ℕ) {x y : A.X n} (hx hy) (e : x = y) : A.cls n x hx = A.cls n y hy := by
  subst e; rfl

def fibIncl (φ : Hom A B) (n : ℕ) : B.Z n →ₗ[R] (fib φ).Z (n+1) where
  toFun b := ⟨(0, b.1), (fib_d_succ_iff φ n _).mpr ⟨map_zero _, by
    show φ.f (n+1) 0 = B.d n b.1
    rw [map_zero]; exact (b.2 : B.d n b.1 = 0).symm⟩⟩
  map_add' x y := Subtype.ext (Prod.ext (add_zero (0 : A.X (n+1))).symm rfl)
  map_smul' r x := Subtype.ext (Prod.ext (smul_zero r).symm rfl)

def fibδ (φ : Hom A B) (n : ℕ) : B.H n →ₗ[R] (fib φ).H (n + 1) :=
  Submodule.mapQ _ _ (fibIncl φ n) fun x hx => by
    change (x : B.X n) ∈ B.B n at hx
    show ((0, (x : B.X n)) : (fib φ).X (n+1)) ∈ (fib φ).B (n+1)
    refine (mem_B_succ (fib φ) n _).mpr ?_
    cases n with
    | zero =>
      rw [mem_B_zero] at hx
      exact ⟨0, by rw [map_zero, hx]; rfl⟩
    | succ m =>
      obtain ⟨y, hy⟩ := (mem_B_succ B m _).mp hx
      refine ⟨(0, -y), Prod.ext (map_zero (A.d (m+1))) ?_⟩
      refine (fib_d_snd_succ φ m _).trans ?_
      show φ.f (m+1) 0 - B.d m (-y) = (x : B.X (m+1))
      rw [map_zero, map_neg, zero_sub, neg_neg, hy]

theorem fibδ_cls (φ : Hom A B) (n : ℕ) (b : B.X n) (hb) (h) :
    fibδ φ n (B.cls n b hb) = (fib φ).cls (n + 1) (0, b) h := rfl

def upMap {B B' : Cx R} (β : Hom B B') : ∀ n, B.up.X n →ₗ[R] B'.up.X n
  | 0 => 0
  | m + 1 => β.f m

def fibMap {A B A' B' : Cx R} (φ : Hom A B) (φ' : Hom A' B') (α : Hom A A') (β : Hom B B')
    (hsq : ∀ n x, β.f n (φ.f n x) = φ'.f n (α.f n x)) : Hom (fib φ) (fib φ') where
  f n := (α.f n).prodMap (upMap β n)
  comm n x := by
    refine Prod.ext (α.comm n x.1) ?_
    cases n with
    | zero =>
      exact (congrArg (β.f 0) (fib_d_snd_zero φ x)).trans ((hsq 0 x.1).trans (fib_d_snd_zero φ' ((α.f 0).prodMap (upMap β 0) x)).symm)
    | succ m =>
      refine (congrArg (β.f (m+1)) (fib_d_snd_succ φ m x)).trans ?_
      refine Eq.trans ?_ (fib_d_snd_succ φ' m _).symm
      show β.f (m+1) (φ.f (m+1) x.1 - B.d m x.2) = φ'.f (m+1) (α.f (m+1) x.1) - B'.d m (β.f m x.2)
      rw [map_sub, hsq]
      exact congrArg (fun t => φ'.f (m+1) (α.f (m+1) x.1) - t) (β.comm m x.2)

def kerMap {A B C : Cx R} (i : Hom A B) (p : Hom B C) (hs : SES i p) : Hom A (fib p) where
  f n := (i.f n).prod 0
  comm n x := by
    refine Prod.ext (i.comm n x) ?_
    cases n with
    | zero => exact ((fib_d_snd_zero p _).trans ((hs.exact 0).apply_apply_eq_zero x)).symm
    | succ m =>
      refine ((fib_d_snd_succ p m _).trans ?_).symm
      show p.f (m+1) (i.f (m+1) x) - C.d m 0 = 0
      rw [map_zero, sub_zero]; exact (hs.exact _).apply_apply_eq_zero x

end ProjectiveLinePlaces

open ProjectiveLinePlaces

end
end ReciprocityTheory.Coh
end

-- bundled from ReciprocityTheory.GroupCohomology.InnerHolds
section
namespace ReciprocityTheory.Coh

open ReciprocityTheory.Gal Cx

universe u

theorem inner_holds : InnerStatement.{u} := by
  intro R _ G _ _ _ M P s hφ hu n
  obtain ⟨e, he, he1, -⟩ := homogIso_holds R G M
  have hcomp : ∀ (n : ℕ) (F : M.coch.X n) (x : Fin (n + 1) → G),
      (e n (P.hom.f n F)).1 x = (e n F).1 fun i => x i * s := by
    intro n F x
    rw [he1, he1]
    show M.rho (x 0) (P.u (F.1 fun i => P.φ ((x i.castSucc)⁻¹ * x i.succ))) =
      M.rho (x 0 * s) (F.1 fun i => (x i.castSucc * s)⁻¹ * (x i.succ * s))
    rw [hu, map_mul]
    first
    | rw [LinearMap.mul_apply]
    | rw [Module.End.mul_apply]
    congr 1
    congr 1
    exact congrArg F.1 (funext fun i => by rw [hφ]; group)
  have key := (prism_holds R G M G G M.coch M.coch e e he he).2 (fun x => x * s) id P.hom
    (Cx.Hom.id M.coch) (continuous_id.mul continuous_const) continuous_id
    (fun g x => by simp only [smul_eq_mul, mul_assoc]) (fun g x => rfl) hcomp
    (fun n F x => rfl) n
  rw [key, Cx.Hom.id_H]

end ReciprocityTheory.Coh
end

-- bundled from ReciprocityTheory.GroupCohomology.IsLowExists
section
namespace ReciprocityTheory.Coh

universe u

theorem exists_isLow {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (M : TRep R G) : ∃ e₀ e₁ e₂, IsLow M e₀ e₁ e₂ := by
  obtain ⟨-, ⟨e₀, h₀⟩, ⟨e₁, h₁⟩, e₂, h₂⟩ := low_holds R G M
  exact ⟨e₀, e₁, e₂, h₀, h₁, h₂⟩

end ReciprocityTheory.Coh
end

-- bundled from ReciprocityTheory.GroupCohomology.Localise
section
namespace ReciprocityTheory.Coh

open ReciprocityTheory.Gal Cx Function

universe u

theorem localise_holds : LocaliseStatement.{u} := by
  intro R _ G _ _ _ _ t L V j hφ hu he hcov n
  obtain ⟨e, he⟩ := he
  refine isLocalized_of_cx j.hom t ?_ ?_ ?_ n
  · intro k x y hxy
    rcases j with ⟨φ, u, hφc, huc, heq⟩
    dsimp only at hφ hu
    subst hφ
    refine Subtype.ext (funext fun g => hu.injective ?_)
    exact congrFun (congrArg Subtype.val hxy) g
  · intro k
    constructor
    · intro x y hxy
      refine Subtype.ext (funext fun g => e.injective ?_)
      rw [he, he]
      exact congrFun (congrArg Subtype.val hxy) g
    · intro y
      refine ⟨⟨fun g => e.symm (y.1 g), e.symm.continuous.comp y.2⟩, Subtype.ext (funext fun g => ?_)⟩
      show t • e.symm (y.1 g) = y.1 g
      rw [← he, e.apply_symm_apply]
  · intro k x
    rcases j with ⟨φ, u, hφc, huc, heq⟩
    dsimp only at hφ hu hcov
    subst hφ
    have hx : Continuous x.1 := x.2
    let O : ℕ → Set (Fin k → G) := fun m => x.1 ⁻¹' ((fun v : V.V => t ^ m • v) ⁻¹' Set.range u)
    have hO : ∀ m, IsOpen (O m) := fun m =>
      ((hu.isOpen_range).preimage (continuous_const_smul _)).preimage hx
    have hmono : Monotone O := by
      refine monotone_nat_of_le_succ fun m g hg => ?_
      obtain ⟨l, hl⟩ := hg
      refine ⟨t • l, ?_⟩
      simp only at hl ⊢
      rw [map_smul, hl, pow_succ', mul_smul]
    have hcover : (Set.univ : Set (Fin k → G)) ⊆ ⋃ m, O m := by
      intro g _
      obtain ⟨m, l, hl⟩ := hcov (x.1 g)
      exact Set.mem_iUnion.2 ⟨m, l, hl⟩
    obtain ⟨m, hm⟩ := isCompact_univ.elim_directed_cover O hO hcover hmono.directed_le
    have hy : ∀ g, u (invFun u (t ^ m • x.1 g)) = t ^ m • x.1 g := fun g =>
      invFun_eq (hm (Set.mem_univ g))
    have hyc : Continuous fun g => invFun u (t ^ m • x.1 g) := by
      rw [hu.isEmbedding.continuous_iff]
      have : (u ∘ fun g => invFun u (t ^ m • x.1 g)) = fun g => t ^ m • x.1 g := funext hy
      rw [this]
      exact hx.const_smul _
    refine ⟨m, ⟨fun g => invFun u (t ^ m • x.1 g), hyc⟩, Subtype.ext (funext fun g => ?_)⟩
    exact hy g

theorem trunc_holds : TruncStatement.{u} := by
  intro R _ A L
  refine ⟨truncCx A L, truncHom A L, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro c hc
    induction c using H_ind with
    | h x hx =>
      rw [Hom.H_cls, cls_eq_zero_iff, mem_B_zero] at hc
      rw [cls_eq_zero_iff, mem_B_zero]
      exact Subtype.ext hc
  · intro c
    induction c using H_ind with
    | h x hx =>
      exact ⟨(truncCx A L).cls 0 ⟨x, Submodule.mem_top⟩ (Subtype.ext hx), rfl⟩
  · rw [injective_iff_map_eq_zero]
    intro c hc
    induction c using H_ind with
    | h x hx =>
      rw [Hom.H_cls, cls_eq_zero_iff, mem_B_succ] at hc
      obtain ⟨y, hy⟩ := hc
      rw [cls_eq_zero_iff, mem_B_succ]
      exact ⟨⟨y, Submodule.mem_top⟩, Subtype.ext hy⟩
  · ext c
    constructor
    · rintro ⟨c', rfl⟩
      induction c' using H_ind with
      | h x hx =>
        rw [Hom.H_cls]
        obtain ⟨_, h⟩ := (mem_truncW_one A L).1 x.2
        exact h
    · intro hc
      obtain ⟨x, hx, rfl⟩ := exists_cls c
      have hm : x ∈ truncW A L 1 := (mem_truncW_one A L).2 ⟨hx, hc⟩
      exact ⟨(truncCx A L).cls 1 ⟨x, hm⟩ (Subtype.ext hx), rfl⟩
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    constructor
    intro a b
    induction a using H_ind with
    | h x hx =>
    induction b using H_ind with
    | h y hy =>
      have h1 : x = 0 := Subtype.ext ((Submodule.mem_bot R).1 x.2)
      have h2 : y = 0 := Subtype.ext ((Submodule.mem_bot R).1 y.2)
      subst h1 h2; rfl

end ReciprocityTheory.Coh
end

-- bundled from ReciprocityTheory.GroupCohomology.LowNat
section
namespace ReciprocityTheory.Coh

open ReciprocityTheory.Gal Cx

universe u

theorem lowNat_holds : LowNatStatement.{u} := by
  intro R _ G _ _ _ G' _ _ _ M M' P e₀ e₁ e₂ e₀' e₁' e₂' hL hL'
  refine ⟨?_, ?_, ?_⟩
  · intro x
    obtain ⟨⟨c, hc⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    apply Subtype.ext
    have hw : M'.coch.d 0 (P.hom.Z 0 ⟨c, hc⟩).1 = 0 := (P.hom.Z 0 ⟨c, hc⟩).2
    have hc' : M.coch.d 0 c = 0 := hc
    change (e₀' (M'.coch.cls 0 (P.hom.Z 0 ⟨c, hc⟩).1 hw) : M'.V) =
      P.u (e₀ (M.coch.cls 0 c hc'))
    have h1 := hL'.1 (P.hom.Z 0 ⟨c, hc⟩).1 hw
    have h2 := hL.1 c hc'
    rw [h1, h2]
    show P.u (c.1 fun i => P.φ (![] i)) = P.u (c.1 ![])
    rw [show (fun i => P.φ (![] i)) = (![] : Fin 0 → G) from funext fun i => i.elim0]
  · intro x
    obtain ⟨⟨c, hc⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨hz, he⟩ := hL.2.1 c hc
    have hw : M'.coch.d 1 (P.hom.Z 1 ⟨c, hc⟩).1 = 0 := (P.hom.Z 1 ⟨c, hc⟩).2
    obtain ⟨hz', he'⟩ := hL'.2.1 (P.hom.Z 1 ⟨c, hc⟩).1 hw
    change e₁' (M'.coch.cls 1 (P.hom.Z 1 ⟨c, hc⟩).1 hw) =
      P.h1 (e₁ (M.coch.cls 1 c hc))
    rw [he', he]
    unfold Pair.h1 pairH1DecompositionMap
    rw [Submodule.mapQ_apply]
    congr 1
    apply Subtype.ext
    funext g
    show P.u (c.1 fun i => P.φ (![g] i)) = P.u (c.1 ![P.φ g])
    rw [show (fun i => P.φ (![g] i)) = ![P.φ g] from by funext i; fin_cases i; rfl]
  · intro x
    obtain ⟨⟨c, hc⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨hz, he⟩ := hL.2.2 c hc
    have hw : M'.coch.d 2 (P.hom.Z 2 ⟨c, hc⟩).1 = 0 := (P.hom.Z 2 ⟨c, hc⟩).2
    obtain ⟨hz', he'⟩ := hL'.2.2 (P.hom.Z 2 ⟨c, hc⟩).1 hw
    change e₂' (M'.coch.cls 2 (P.hom.Z 2 ⟨c, hc⟩).1 hw) =
      P.h2 (e₂ (M.coch.cls 2 c hc))
    rw [he', he]
    unfold Pair.h2 compatiblePairH2
    rw [Submodule.mapQ_apply]
    congr 1
    apply Subtype.ext
    funext g
    show P.u (c.1 fun i => P.φ (![g.1, g.2] i)) = P.u (c.1 ![P.φ g.1, P.φ g.2])
    rw [show (fun i => P.φ (![g.1, g.2] i)) = ![P.φ g.1, P.φ g.2] from by
      funext i; fin_cases i <;> rfl]

end ReciprocityTheory.Coh
end

