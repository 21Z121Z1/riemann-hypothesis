import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle0004
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpecHolds
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SplitsSelfOfIso
import Development.EtaleCohomology.WeilConjectures.Bundle0002

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTwGal
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

theorem UpperTheory.Gal.G3.pTwGal :
    TwSplit → TwGal := by
  intro hS B G _ X m j b hnorm
  classical
  haveI hN : ((X.K m).subgroupOf (X.K j)).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    push_cast
    exact hnorm g g.2 n hn⟩
  haveI : Finite (X.K j ⧸ (X.K m).subgroupOf (X.K j)) := Nat.finite_of_card_ne_zero (X.idx m j)
  have admr : ∀ c : X.K j ⧸ (X.K m).subgroupOf (X.K j), X.admitted m m ((c.out : X.K j) : G)⁻¹ := fun c =>
    ⟨X.K_le j _ (inv_mem c.out.2), fun u hu => hnorm _ (inv_mem c.out.2) u hu⟩
  have uniq : ∀ k ∈ X.K j, ∃! c : X.K j ⧸ (X.K m).subgroupOf (X.K j),
      k * (((c.out : X.K j) : G))⁻¹⁻¹ ∈ X.K m := by
    intro k hk
    refine ⟨QuotientGroup.mk ⟨k⁻¹, inv_mem hk⟩, ?_, ?_⟩
    · obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul ((X.K m).subgroupOf (X.K j)) (⟨k⁻¹, inv_mem hk⟩ : X.K j)
      simp only [inv_inv]
      rw [hu]
      have hu' : ((u : X.K j) : G) ∈ X.K m := Subgroup.mem_subgroupOf.mp u.2
      simpa [mul_assoc] using hu'
    · intro c hc
      simp only [inv_inv] at hc
      rw [← QuotientGroup.out_eq' c, QuotientGroup.eq, Subgroup.mem_subgroupOf]
      simpa [mul_inv_rev] using inv_mem hc
  have trc : ∀ (g1 g2 : G) (e : g1 = g2) (p1 : X.admitted m m g1) (p2 : X.admitted m m g2),
      X.tr m m g1 p1.1 p1.2 = X.tr m m g2 p2.1 p2.2 := by
    intro g1 g2 e p1 p2
    subst e
    rfl
  have tl : ∀ (g k : G) (hg : X.admitted m m g) (hk : k ∈ X.K m) (hkg : X.admitted m m (k * g)),
      X.tr m m (k * g) hkg.1 hkg.2 = X.tr m m g hg.1 hg.2 := by
    intro g k hg hk hkg
    rw [← X.tr_mul m m m g k hg.1 hg.2 (X.K_le m k hk) (X.tower_admissible_self hk).2 hkg.1 hkg.2,
      X.tr_self m k _ _ hk, Category.comp_id]
  refine ⟨X.K j ⧸ (X.K m).subgroupOf (X.K j), inferInstance, inferInstance,
    fun c => ((c.out : X.K j) : G)⁻¹, admr, fun c => inv_mem c.out.2, uniq, ?_⟩
  unfold GlobalTheory.GalV.IsGalois
  refine ⟨X.fin m j b.1 b.2, X.etale m j b.1 b.2, X.onto m j b.1 b.2, ?_, ?_,
    hS X m m j b b le_rfl hnorm _ _ admr (fun c => inv_mem c.out.2) uniq⟩
  · have h1 : ((1 : X.K j ⧸ (X.K m).subgroupOf (X.K j)).out : G) ∈ X.K m :=
      Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp (QuotientGroup.out_eq' 1))
    exact X.tr_self m _ _ _ (inv_mem h1)
  · intro g g'
    set w : X.K j := ((g.out : X.K j) * g'.out)⁻¹ * (g * g').out with hwdef
    have hw : w ∈ (X.K m).subgroupOf (X.K j) := by
      rw [hwdef, ← QuotientGroup.eq, QuotientGroup.mk_mul, QuotientGroup.out_eq', QuotientGroup.out_eq',
        QuotientGroup.out_eq']
    have hw' : ((w : X.K j) : G) ∈ X.K m := Subgroup.mem_subgroupOf.mp hw
    have e : (((g * g').out : X.K j) : G)⁻¹ =
        ((w : X.K j) : G)⁻¹ * ((((g'.out : X.K j) : G))⁻¹ * (((g.out : X.K j) : G))⁻¹) := by
      simp only [hwdef, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    have hA : X.admitted m m ((((g'.out : X.K j) : G))⁻¹ * (((g.out : X.K j) : G))⁻¹) :=
      Tower.admitted.mul (admr g) (admr g')
    have hB : X.admitted m m (((w : X.K j) : G)⁻¹ * ((((g'.out : X.K j) : G))⁻¹ * (((g.out : X.K j) : G))⁻¹)) :=
      Tower.admitted.mul hA (X.tower_admissible_self (inv_mem hw'))
    exact ((trc _ _ e (admr (g * g')) hB).trans (tl _ _ hA (inv_mem hw') hB)).trans
      (X.tr_mul m m m _ _ (admr g).1 (admr g).2 (admr g').1 (admr g').2 hA.1 hA.2).symm
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTwSplit
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

private theorem tr_left {B : Scheme.{0}} {G : Type} [Group G] (X : Tower B G) {i j : X.ι} {h k : G} (hk : k ∈ X.K j)
    (a : X.admitted i j h) (p q) : X.tr i j (k * h) p q = X.tr i j h a.1 a.2 := by
  rw [← X.tr_mul i j j h k a.1 a.2 (X.K_le j k hk) (X.tower_admissible_self hk).2 p q,
    X.tr_self j k _ _ hk, Category.comp_id]

private theorem tower_tr_eq_of_eq_mul_of_mem_K {B : Scheme.{0}} {G : Type} [Group G] (X : Tower B G) {i j : X.ι} {h k g : G}
    (hk : k ∈ X.K j) (a : X.admitted i j h) (hg : g = k * h) (p q) : X.tr i j g p q = X.tr i j h a.1 a.2 := by
  subst hg
  exact tr_left X hk a p q

private theorem tower_tr_comp_tr_eq_tr_mul {B : Scheme.{0}} {G : Type} [Group G] (X : Tower B G) {i j m : X.ι} {h h' : G}
    (p : h ∈ X.Δ) (q : ∀ u ∈ X.K i, h * u * h⁻¹ ∈ X.K j) (p' : h' ∈ X.Δ)
    (q' : ∀ u ∈ X.K j, h' * u * h'⁻¹ ∈ X.K m) :
    X.tr i j h p q ≫ X.tr j m h' p' q' =
      X.tr i m (h' * h) (Tower.admitted.mul (X := X) ⟨p, q⟩ ⟨p', q'⟩).1
        (Tower.admitted.mul (X := X) ⟨p, q⟩ ⟨p', q'⟩).2 :=
  X.tr_mul _ _ _ _ _ _ _ _ _ _ _

theorem UpperTheory.Gal.G3.pTwSplit :
    SplitsPts → TwSplit := by
  intro hS B G _ X m i j a b hmi hnorm J _ r c hr huniq
  have hij : ∀ u ∈ X.K i, u ∈ X.K j := fun u hu => by simpa using a.2 u hu
  have hmj : ∀ u ∈ X.K m, u ∈ X.K j := fun u hu => by simpa using b.2 u hu
  have Am : ∀ g ∈ X.K j, X.admitted m m g := fun g hg => ⟨X.K_le j g hg, fun u hu => hnorm g hg u hu⟩
  have hcomp : ∀ x, X.tr m i (r x) (c x).1 (c x).2 ≫ X.tr i j 1 a.1 a.2 = X.tr m j 1 b.1 b.2 := by
    intro x
    rw [X.tr_mul m i j (r x) 1 (c x).1 (c x).2 a.1 a.2 ((c x).mul a).1 ((c x).mul a).2]
    exact tower_tr_eq_of_eq_mul_of_mem_K X (hr x) b (by simp) _ _
  have U : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : sp Ω ⟶ X.Z m) (x1 x2 : J),
      x ≫ X.tr m i (r x1) (c x1).1 (c x1).2 = x ≫ X.tr m i (r x2) (c x2).1 (c x2).2 → x1 = x2 := by
    intro Ω _ _ x x1 x2 h12
    have p1 := X.isAdmissibleIntegralBasisChange_one hmi
    have e1 : (x ≫ X.tr m m (r x1) (Am _ (hr x1)).1 (Am _ (hr x1)).2) ≫ X.tr m i 1 p1.1 p1.2
        = (x ≫ X.tr m m (r x2) (Am _ (hr x2)).1 (Am _ (hr x2)).2) ≫ X.tr m i 1 p1.1 p1.2 := by
      rw [Category.assoc, Category.assoc, tower_tr_comp_tr_eq_tr_mul, tower_tr_comp_tr_eq_tr_mul,
        tower_tr_eq_of_eq_mul_of_mem_K X (one_mem (X.K i)) (c x1) (rfl : (1:G) * r x1 = 1 * r x1),
        tower_tr_eq_of_eq_mul_of_mem_K X (one_mem (X.K i)) (c x2) (rfl : (1:G) * r x2 = 1 * r x2)]
      exact h12
    obtain ⟨k, hki, a', b', hk⟩ := X.trans m i p1.1 p1.2
      (fun k hk u hu => hnorm k (hij k hk) u hu) Ω _ _ e1
    have hkj := hij k hki
    have e2 : x ≫ X.tr m m (r x2) (Am _ (hr x2)).1 (Am _ (hr x2)).2
        = x ≫ X.tr m m (k * r x1) (Am _ (mul_mem hkj (hr x1))).1 (Am _ (mul_mem hkj (hr x1))).2 := by
      rw [hk, Category.assoc, tower_tr_comp_tr_eq_tr_mul]
    have hinv : (r x2)⁻¹ ∈ X.K j := inv_mem (hr x2)
    have hg : (r x2)⁻¹ * (k * r x1) ∈ X.K j := mul_mem hinv (mul_mem hkj (hr x1))
    have hfix : x ≫ X.tr m m _ (Am _ hg).1 (Am _ hg).2 = x := by
      rw [← X.tr_mul m m m (k * r x1) (r x2)⁻¹ (Am _ (mul_mem hkj (hr x1))).1 (Am _ (mul_mem hkj (hr x1))).2
        (Am _ hinv).1 (Am _ hinv).2, ← Category.assoc, ← e2, Category.assoc,
        X.tr_mul m m m (r x2) (r x2)⁻¹ (Am _ (hr x2)).1 (Am _ (hr x2)).2 (Am _ hinv).1 (Am _ hinv).2
          (Am _ (mul_mem hinv (hr x2))).1 (Am _ (mul_mem hinv (hr x2))).2,
        X.tr_self m _ _ _ (by simp), Category.comp_id]
    have hgm := X.free m j (fun u hu => hmj u hu) _ hg (Am _ hg).1 (Am _ hg).2 Ω x hfix
    have hk0 : k * r x1 ∈ X.K j := mul_mem hkj (hr x1)
    apply (huniq _ hk0).unique
    · simpa using hki
    · have := (c x2).2 _ hgm
      convert this using 1
      group
  have hpts : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : sp Ω ⟶ X.Z m) (y : sp Ω ⟶ X.Z i),
      y ≫ X.tr i j 1 a.1 a.2 = x ≫ X.tr m j 1 b.1 b.2 → ∃! x0, x ≫ X.tr m i (r x0) (c x0).1 (c x0).2 = y := by
    intro Ω _ _ x y hxy
    have p1 := X.isAdmissibleIntegralBasisChange_one hmi
    haveI := X.fin m i p1.1 p1.2
    obtain ⟨v, hv⟩ := (X.onto m i p1.1 p1.2).surj (UpperTheory.Gal.TranscendenceTraces.pt (X := X.Z i) (Ω := Ω) y)
    obtain ⟨z, hz, -⟩ := UpperTheory.Gal.TranscendenceTraces.ptLift_holds (X.tr m i 1 p1.1 p1.2) Ω y v hv
    have hzj : x ≫ X.tr m j 1 b.1 b.2 = z ≫ X.tr m j 1 b.1 b.2 := by
      rw [← hxy, ← hz, Category.assoc, tower_tr_comp_tr_eq_tr_mul,
        tower_tr_eq_of_eq_mul_of_mem_K X (one_mem (X.K j)) b (rfl : (1:G) * 1 = 1 * 1)]
    obtain ⟨k, hkj, a', b', hk⟩ := X.trans m j b.1 b.2 hnorm Ω x z hzj
    obtain ⟨x0, hx0, -⟩ := huniq k hkj
    have ex : x ≫ X.tr m i (r x0) (c x0).1 (c x0).2 = y := by
      rw [← hz, hk, Category.assoc, tower_tr_comp_tr_eq_tr_mul,
        tower_tr_eq_of_eq_mul_of_mem_K X hx0 (c x0) (show (1:G) * k = k * (r x0)⁻¹ * r x0 by group)]
    exact ⟨x0, ex, fun x2 h2 => U Ω x x2 x0 (h2.trans ex.symm)⟩
  haveI := X.fin i j a.1 a.2
  haveI := X.etale i j a.1 a.2
  exact hS _ _ J _ hcomp hpts
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitDesc
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV

namespace UpperTheory.Gal.G3

abbrev FinSub (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] : Type := {L : IntermediateField k Ω // FiniteDimensional k L}

def finDiag (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] : FinSub k Ω ⥤ Under (CommRingCat.of k) where
  obj L := Under.mk (CommRingCat.ofHom (algebraMap k L.1))
  map {L M} h := Under.homMk (CommRingCat.ofHom (IntermediateField.inclusion (show L.1 ≤ M.1 from h.le)).toRingHom)

def finCocone (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] : Cocone (finDiag k Ω ⋙ Under.forget _) where
  pt := CommRingCat.of Ω
  ι := { app := fun L => CommRingCat.ofHom (algebraMap L.1 Ω) }

def FinColim : Prop := ∀ (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [Algebra.IsAlgebraic k Ω],
  IsFiltered (FinSub k Ω) ∧ Nonempty (IsColimit (finCocone k Ω))

def VDesc : Prop := ∀ (q : ℕ) (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [Algebra.IsAlgebraic k Ω] {X : Scheme.{0}}
  (p : X ⟶ sp k) [QuasiCompact p] [QuasiSeparated p] (n i : ℤ) (y : Ht q (sch.obj (geom Ω p)) n i),
  ∃ (L : IntermediateField k Ω) (_ : FiniteDimensional k L) (z : Ht q (sch.obj (geom L p)) n i),
    pull _ (sch.map (LateralTheory.EWeil.StabPf.proj L p)) _ n z = y

def VStab : Prop := ∀ (l : ℕ) [Fact l.Prime] (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [Algebra.IsAlgebraic k Ω]
  {X : Scheme.{0}} (p : X ⟶ sp k) [QuasiCompact p] [QuasiSeparated p] (n i : ℤ) (x : Hl l (sch.obj (geom Ω p)) n i) (m : ℕ),
  IsOpen {σ : Ω ≃ₐ[k] Ω | (galHl l Ω p n i σ x).1 m = x.1 m}

def SplitDesc : Prop := ∀ {Z Y W : Scheme.{0}} (s : Y ⟶ Z) (c : W ⟶ Z) [IsFinite c] [Etale c] [Surjective c] (J : Type) [Finite J]
  (σ : J → (W ⟶ Y)), Splits s c σ → IsFinite s ∧ Etale s

def CharVan : Prop := ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k], (l : k) = 0 → ∀ {X : Scheme.{0}} (_ : X ⟶ sp k) (n i : ℤ),
  Subsingleton (Hl l (sch.obj X) n i)

def CorrUniq : Prop := ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] {Z Y Z' : Scheme.{0}} (_ : Z ⟶ sp k) (s : Y ⟶ Z) (t : Y ⟶ Z')
  (A A' : Htot l (sch.obj Z') →ₗ[ℚ_[l]] Htot l (sch.obj Z)), IsCorrOp l s t A → IsCorrOp l s t A' → A = A'

def CorrConj : Prop := ∀ (l : ℕ) [Fact l.Prime] {Z Y Z' : Scheme.{0}} (s : Y ⟶ Z) (t : Y ⟶ Z') (a : Z ⟶ Z) (b : Y ⟶ Y) (a' : Z' ⟶ Z')
  [IsIso a] [IsIso b] [IsIso a'], s ≫ a = b ≫ s → t ≫ a' = b ≫ t →
  ∀ A : Htot l (sch.obj Z') →ₗ[ℚ_[l]] Htot l (sch.obj Z), IsCorrOp l s t A →
    IsCorrOp l s t (pullTot l (sch.map a) ∘ₗ A ∘ₗ pullTot l (sch.map (inv a')))

def VInvU : Prop := ∀ (l : ℕ) [Fact l.Prime] {Y X : Scheme.{0}} (f : Y ⟶ X), IsUnit (l : Γ(X, ⊤)) → ∀ (G : Type) [Group G] [Finite G]
  (a : G → (Y ⟶ Y)), IsGalois f G a → ∀ n i : ℤ, Function.Injective (pullHQ l (sch.map f) n i) ∧
  LinearMap.range (pullHQ l (sch.map f) n i) = ⨅ g, LinearMap.ker (pullHQ l (sch.map (a g)) n i - LinearMap.id)

def VBcS : Prop := ∀ (l : ℕ) [Fact l.Prime] (k Ω : Type) [Field k] [IsAlgClosed k] [Field Ω] [IsAlgClosed Ω] (φ : k →+* Ω),
  IsUnit (l : k) → ∀ {X : Scheme.{0}} (p : X ⟶ sp k) [IsProper p] [Smooth p] (n i : ℤ),
  Function.Bijective (pullHQ l (sch.map (pullback.fst p (Spec.map (CommRingCat.ofHom φ)))) n i)

end UpperTheory.Gal.G3

end
end

