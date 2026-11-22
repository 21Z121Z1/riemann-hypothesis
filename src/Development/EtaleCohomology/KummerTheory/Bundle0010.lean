import Development.EtaleCohomology.KummerTheory.Bundle0002
import Development.EtaleCohomology.KummerTheory.Bundle0003
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing

-- bundled from Development.EtaleCohomology.KummerTheory.RedKerPf
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.KummerTheory.RedKerPf

open LateralTheory.KummerTheory.BockCut

theorem sepLoc {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} (y z : Sec F U)
    (h : Loc U fun V g => Sec.res g y = Sec.res g z) : y = z := by
  obtain ⟨S, hS, hh⟩ := h
  have h1 := (isSheaf_iff_isSheaf_of_type _ _).1
    ((Presheaf.isSheaf_iff_isSheaf_forget _ F.obj (forget (ModuleCat.{1} (ULift.{1} R)))).1 F.cond)
  exact (h1 S hS).isSeparatedFor.ext (fun V g hg => hh V g hg)

theorem locZero {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} (hL : LateralTheory.EtaleFoundations.EtaleLocalPropertyBasicClosure)
    (y : Sec F U) (h : Loc U fun V g => Sec.res g y = 0) : y = 0 := by
  refine sepLoc y 0 (hL.2.1 U _ _ h fun V g hg => ?_)
  rw [hg]; exact (map_zero _).symm

theorem secEmpty {R : Type} [CommRing R] {F : Shv R} {V : Scheme.{0}} [IsEmpty V]
    (hL : LateralTheory.EtaleFoundations.EtaleLocalPropertyBasicClosure) (y : Sec F V) : y = 0 :=
  sepLoc y 0 (hL.2.2.2.2.2.2 V _)

theorem resMap {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) :=
  (congrArg (fun f => (ModuleCat.Hom.hom f) x) (φ.hom.naturality g.op)).symm

theorem resNsmul {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (n : ℕ) (x : Sec F U) :
    Sec.res g (n • x) = n • Sec.res g x := map_nsmul _ _ _

theorem mapNsmul {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (n : ℕ) (x : Sec F U) :
    Sec.map φ (n • x) = n • Sec.map φ x := map_nsmul _ _ _

theorem killTw {q : ℕ} {i : ℤ} {U : Scheme.{0}} (x : Sec (tw q i) U) : q • x = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]
  have : ((q : ℕ) : ULift.{1} (ZMod q)) = 0 := by ext; simp
  rw [this, zero_smul]

theorem kill {q : ℕ} {i : ℤ} {U : Scheme.{0}} (x : Sec (TZ q i) U) : q • x = 0 := killTw (i := i) x

theorem mapGen (hT : LateralTheory.EtaleFoundations.EtaleTateTwistSectionsLocallyGenerated) (hP : LateralTheory.EtaleFoundations.PrimitiveRootsOfUnityBasicIdentities)
    (Q e q : ℕ) [NeZero Q] [NeZero q] (hQ : Q = e * q) (i : ℤ) (π : TZ Q i ⟶ TZ q i) (hπ : IsRed Q q i π)
    (V : Scheme.{0}) [Nonempty V] (ζ : Prim Q Γ(V, ⊤)) (c : ℕ) :
    Sec.map π (c • genZ i ζ) = 0 ↔ q ∣ c := by
  obtain ⟨ξ, hξ⟩ := (hP Q Γ(V, ⊤)).2.2.2.2.2 q ⟨e, by rw [hQ, mul_comm]⟩ ζ
  rw [mapNsmul, hπ V ζ ξ hξ]
  constructor
  · intro h; exact (hT q i).2.2.1 V ξ c h
  · rintro ⟨k, rfl⟩
    rw [mul_comm, mul_smul, kill, smul_zero]

theorem eGen (hT : LateralTheory.EtaleFoundations.EtaleTateTwistSectionsLocallyGenerated)
    (Q e q : ℕ) [NeZero Q] (hQ : Q = e * q) (i : ℤ)
    (V : Scheme.{0}) [Nonempty V] (ζ : Prim Q Γ(V, ⊤)) (c : ℕ) :
    e • (c • genZ i ζ) = 0 ↔ q ∣ c := by
  have he : 0 < e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · exact absurd (by rw [hQ, h, zero_mul]) (NeZero.ne Q)
    · exact h
  rw [← mul_smul]
  constructor
  · intro h
    have := (hT Q i).2.2.1 V ζ (e * c) h
    rw [hQ] at this
    exact (Nat.mul_dvd_mul_iff_left he).1 this
  · rintro ⟨k, rfl⟩
    have : e * (q * k) = Q * k := by rw [hQ]; ring
    rw [this, mul_comm, mul_smul, kill, smul_zero]

theorem RedKer_of (hT : LateralTheory.EtaleFoundations.EtaleTateTwistSectionsLocallyGenerated) (hP : LateralTheory.EtaleFoundations.PrimitiveRootsOfUnityBasicIdentities)
    (hL : LateralTheory.EtaleFoundations.EtaleLocalPropertyBasicClosure) : RedKer := by
  intro Q e q _ hQ i π hπ U y
  haveI : NeZero q := ⟨by rintro rfl; exact NeZero.ne Q (by rw [hQ, mul_zero])⟩
  have L := (hT Q i).1 U y

  have key : Sec.map π y = 0 → Loc U fun V g => Sec.res g y = 0 ∨ (Nonempty V ∧ ∃ (ζ : Prim Q Γ(V, ⊤)) (c : ℕ),
      q ∣ c ∧ Sec.res (F := TZ Q i) g y = c • genZ i ζ) ∨ IsEmpty V := by
    intro h0
    refine hL.2.1 U _ _ L fun V g hg => ?_
    rcases hg with hg | ⟨ζ, c, hc⟩
    · exact Or.inl hg
    rcases isEmpty_or_nonempty V with hV | hV
    · exact Or.inr (Or.inr hV)
    refine Or.inr (Or.inl ⟨hV, ζ, c, ?_, hc⟩)
    have h1 : Sec.map π (Sec.res (F := TZ Q i) g y) = 0 := by rw [← resMap, h0]; exact map_zero _
    have hc' : Sec.res (F := TZ Q i) g y = c • genZ i ζ := hc
    rw [hc'] at h1
    exact (mapGen hT hP Q e q hQ i π hπ V ζ c).1 h1
  refine ⟨⟨fun h0 => ?_, fun h0 => ?_⟩, fun h0 => ?_⟩
  · refine locZero hL _ (hL.2.1 U _ _ (key h0) fun V g hg => ?_)
    rw [resNsmul]
    rcases hg with hg | ⟨hV, ζ, c, hc, hg⟩ | hV
    · rw [hg]; exact smul_zero _
    · rw [hg]; exact (eGen hT Q e q hQ i V ζ c).2 hc
    · exact secEmpty hL _
  · refine locZero hL _ (hL.2.1 U _ _ L fun V g hg => ?_)
    rw [resMap]
    rcases hg with hg | ⟨ζ, c, hc⟩
    · have hg' : Sec.res (F := TZ Q i) g y = 0 := hg
      rw [hg']; exact map_zero _
    rcases isEmpty_or_nonempty V with hV | hV
    · exact secEmpty hL _
    have hc' : Sec.res (F := TZ Q i) g y = c • genZ i ζ := hc
    have h1 : e • Sec.res (F := TZ Q i) g y = 0 := by rw [← resNsmul, h0]; exact map_zero _
    rw [hc'] at h1 ⊢
    exact (mapGen hT hP Q e q hQ i π hπ V ζ c).2 ((eGen hT Q e q hQ i V ζ c).1 h1)
  · refine hL.2.1 U _ _ (key h0) fun V g hg => ?_
    rcases hg with hg | ⟨hV, ζ, c, ⟨k, rfl⟩, hg⟩ | hV
    · exact ⟨0, by rw [hg]; exact smul_zero _⟩
    · exact ⟨k • genZ i ζ, by rw [hg, ← mul_smul]⟩
    · exact ⟨0, by rw [smul_zero]; exact (secEmpty hL _).symm⟩

end LateralTheory.KummerTheory.RedKerPf
end

-- bundled from Development.EtaleCohomology.KummerTheory.RedPostPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.KummerTheory.RedPostPf
open LateralTheory.KummerTheory.BockCut

variable {S R T : Type} [CommRing S] [CommRing R] [CommRing T]

theorem sec_nat {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (a : Sec F U) :
    Sec.res g (Sec.map φ a) = Sec.map φ (Sec.res g a) := by
  have h := φ.hom.naturality g.op
  exact (congrArg (fun f => f.hom a) h).symm

theorem sec_comp {F G M : Shv R} (φ : F ⟶ G) (ψ : G ⟶ M) {U : Scheme.{0}} (a : Sec F U) :
    Sec.map (φ ≫ ψ) a = Sec.map ψ (Sec.map φ a) := rfl

def scomp {I : Cx S} {J : Cx R} {K : Cx T} (ρ : SemiMap I J) (σ : SemiMap J K) : SemiMap I K where
  app U s := (σ.app U s).comp (ρ.app U s)
  nat g s a := by simp only [AddMonoidHom.comp_apply]; rw [σ.nat, ρ.nat]
  comm U s t a := by simp only [AddMonoidHom.comp_apply]; rw [σ.comm, ρ.comm]

def spost {I : Cx S} {J J' : Cx R} (ρ : SemiMap I J) (u : J ⟶ J') : SemiMap I J' where
  app U s := ((u.f s).hom.app (op U)).hom.toAddMonoidHom.comp (ρ.app U s)
  nat g s a := by
    change Sec.res g (Sec.map (u.f s) (ρ.app _ s a)) = Sec.map (u.f s) (ρ.app _ s (Sec.res g a))
    rw [sec_nat, ρ.nat]
  comm U s t a := by
    change Sec.map (J'.d s t) (Sec.map (u.f s) (ρ.app U s a)) = Sec.map (u.f t) (ρ.app U t (Sec.map (I.d s t) a))
    rw [← ρ.comm, ← sec_comp, ← sec_comp, u.comm]

theorem scomp_op (hS : LateralTheory.EtaleFoundations.EtaleCochainSemilinearMapOnClasses) {I : Cx S} {J : Cx R} {K : Cx T} (ρ : SemiMap I J)
    (σ : SemiMap J K) (E : Spc) (n : ℤ) (x : CohomologyClass ((chains S).obj E) I n) :
    (scomp ρ σ).op.app E n x = σ.op.app E n (ρ.op.app E n x) := by
  obtain ⟨α, rfl⟩ := CohomologyClass.mk_surjective x
  obtain ⟨β, hβ⟩ := (hS S R ρ).1 E n α
  obtain ⟨γ, hγ⟩ := (hS R T σ).1 E n β
  rw [(hS S R ρ).2 E n α β hβ, (hS R T σ).2 E n β γ hγ, (hS S T (scomp ρ σ)).2 E n α γ ?_]
  intro p s h U y
  rw [hγ, hβ]
  rfl

end LateralTheory.KummerTheory.RedPostPf

namespace LateralTheory.KummerTheory.RedPostPf
open LateralTheory.KummerTheory.BockCut

variable {S R : Type} [CommRing S] [CommRing R]

def up {F : Shv S} (φ : R →+* S) {U : Scheme.{0}} (a : Sec ((restr φ).obj F) U) : Sec F U := a

theorem up_add {F : Shv S} (φ : R →+* S) {U : Scheme.{0}} (a b : Sec ((restr φ).obj F) U) :
    up φ (a + b) = up φ a + up φ b := rfl

theorem up_res {F : Shv S} (φ : R →+* S) {V U : Scheme.{0}} (g : V ⟶ U) (a : Sec ((restr φ).obj F) U) :
    Sec.res g (up φ a) = up φ (Sec.res g a) := rfl

theorem sec_add {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (a b : Sec F U) :
    Sec.map φ (a + b) = Sec.map φ a + Sec.map φ b := map_add _ _ _

theorem RedPost_of (hU : SemiUniq) (hE : TwExt) (hZ : ZHom) (hS : LateralTheory.EtaleFoundations.EtaleCochainSemilinearMapOnClasses)
    (hC : LateralTheory.EtaleFoundations.EtaleCochainSemilinearMapCompCompatible) (hR : LateralTheory.EtaleFoundations.EtaleRootsOfUnityReductionMapGenerator) (hX : LateralTheory.EtaleFoundations.EtaleRestrictScalarsResolutionCompatible)
    (hP : LateralTheory.EtaleFoundations.PrimitiveRootsOfUnityBasicIdentities) (hB : LateralTheory.EtaleFoundations.EtaleInjectiveResolutionBasicProperties) : RedPost := by
  intro Q q _ hq i π hπ E n x
  have : NeZero q := ⟨ne_zero_of_dvd_ne_zero (NeZero.ne Q) hq⟩
  let ρ := scomp (redMap Q q i) (restrMap (Int.castRingHom (ZMod q)) (tw q i))
  let r0 := restrMap (Int.castRingHom (ZMod Q)) (tw Q i)
  let ρ' := spost r0 (resMap ℤ π)
  have h1 : restrH (Int.castRingHom (ZMod q)) E (tw q i) n (red Q q E n i x) = ρ.op.app E n x :=
    (scomp_op hS _ _ E n x).symm
  have h2 : HK.post ℤ ((chains ℤ).obj E) π n (restrH (Int.castRingHom (ZMod Q)) E (tw Q i) n x) = ρ'.op.app E n x :=
    ((hC (ZMod Q) ℤ r0 ρ' (resMap ℤ π) (fun _ _ _ => rfl)).1 E n x).symm
  rw [h1, h2]
  obtain ⟨φ1, hφ1⟩ := hZ (TZ Q i) ((res ℤ (TZ q i)).X 0)
    (fun U => AddMonoidHom.mk' (fun a : Sec (TZ Q i) U => ρ.app U 0 (Sec.map (resι _ (tw Q i)) (up _ a)))
      (fun a b => by rw [up_add, sec_add, map_add]))
    (fun V U g a => by
      change Sec.res g (ρ.app U 0 (Sec.map (resι _ (tw Q i)) (up _ a))) = ρ.app V 0 (Sec.map (resι _ (tw Q i)) (up _ (Sec.res g a)))
      rw [ρ.nat, sec_nat, up_res])
  obtain ⟨φ2, hφ2⟩ := hZ (TZ Q i) ((res ℤ (TZ q i)).X 0)
    (fun U => AddMonoidHom.mk' (fun a : Sec (TZ Q i) U => ρ'.app U 0 (Sec.map (resι _ (tw Q i)) (up _ a)))
      (fun a b => by rw [up_add, sec_add, map_add]))
    (fun V U g a => by
      change Sec.res g (ρ'.app U 0 (Sec.map (resι _ (tw Q i)) (up _ a))) = ρ'.app V 0 (Sec.map (resι _ (tw Q i)) (up _ (Sec.res g a)))
      rw [ρ'.nat, sec_nat, up_res])
  have heq : φ1 = φ2 := by
    refine hE Q i _ φ1 φ2 fun U ζ => ?_
    obtain ⟨ξ, hξ⟩ := (hP Q Γ(U, ⊤)).2.2.2.2.2 q hq ζ
    rw [hφ1, hφ2]
    change (restrMap (Int.castRingHom (ZMod q)) (tw q i)).app U 0 ((redMap Q q i).app U 0 (resGen i ζ)) =
      Sec.map ((resMap ℤ π).f 0) (r0.app U 0 (Sec.map (resι _ (tw Q i)) (twGen i ζ)))
    rw [hR Q q hq i U ζ ξ hξ, hX ℤ (ZMod Q) _ (tw Q i) U (twGen i ζ)]
    change (restrMap (Int.castRingHom (ZMod q)) (tw q i)).app U 0 (Sec.map (resι _ (tw q i)) (twGen i ξ)) = _
    rw [hX ℤ (ZMod q) _ (tw q i) U (twGen i ξ), ← sec_comp, ((hB ℤ (TZ Q i)).2.2.2.2.2.2.2 (TZ q i) π).2, sec_comp]
    exact congrArg (Sec.map (resι ℤ (TZ q i))) (hπ U ζ ξ hξ).symm
  refine hU (ZMod Q) (tw Q i) (TZ q i) ρ ρ' (fun U a => ?_) E n x
  have e1 := hφ1 U a
  have e2 := hφ2 U a
  rw [heq] at e1
  exact e1.symm.trans e2

end LateralTheory.KummerTheory.RedPostPf
end
end

-- bundled from Development.EtaleCohomology.KummerTheory.SHInsepHensPf
section
noncomputable section
open scoped TensorProduct
open GlobalTheory.EtC IsLocalRing Polynomial

namespace LateralTheory.KummerTheory

theorem hens_root_of_sub {R S : Type*} [CommRing R] [CommRing S] [HenselianLocalRing R] [IsLocalRing S]
    (φ : R →+* S) (hc : (maximalIdeal S).comap φ = maximalIdeal R) (f : S[X]) (hf : f.Monic) (a₀ : S)
    (hlift : ∀ n, f.coeff n ∈ Set.range φ) (ha : a₀ ∈ Set.range φ) (h1 : f.eval a₀ ∈ maximalIdeal S)
    (h2 : IsUnit (f.derivative.eval a₀)) : ∃ a, f.IsRoot a ∧ a - a₀ ∈ maximalIdeal S := by
  obtain ⟨g, hg, -, hgm⟩ := lifts_and_degree_eq_and_monic ((lifts_iff_coeff_lifts f).2 hlift) hf
  obtain ⟨b₀, rfl⟩ := ha
  have hmem : ∀ x, x ∈ maximalIdeal R ↔ φ x ∈ maximalIdeal S := fun x => by rw [← hc]; rfl
  have e1 : φ (g.eval b₀) = f.eval (φ b₀) := by rw [← hg, eval_map, eval₂_at_apply]
  have e2 : φ (g.derivative.eval b₀) = f.derivative.eval (φ b₀) := by
    rw [← hg, derivative_map, eval_map, eval₂_at_apply]
  have hu : IsUnit (g.derivative.eval b₀) := by
    by_contra hu
    have := (hmem _).1 ((mem_maximalIdeal _).2 hu)
    rw [e2] at this
    exact (mem_maximalIdeal _).1 this h2
  obtain ⟨b, hb, hbb⟩ := HenselianLocalRing.is_henselian g hgm b₀ ((hmem _).2 (e1 ▸ h1)) hu
  refine ⟨φ b, ?_, ?_⟩
  · rw [IsRoot.def] at hb ⊢
    rw [← hg, eval_map, eval₂_at_apply, hb, map_zero]
  · rw [← map_sub]; exact (hmem _).1 hbb

abbrev incMap (κ K A : Type) [Field κ] [Field K] [Algebra κ K] [CommRing A] [Algebra κ A]
    (L : IntermediateField κ K) : A ⊗[κ] L →ₐ[A] A ⊗[κ] K :=
  Algebra.TensorProduct.map (AlgHom.id A A) L.val

theorem incMap_mono {κ K A : Type} [Field κ] [Field K] [Algebra κ K] [CommRing A] [Algebra κ A]
    {L L' : IntermediateField κ K} (h : L ≤ L') {x : A ⊗[κ] K} (hx : x ∈ (incMap κ K A L).range) :
    x ∈ (incMap κ K A L').range := by
  obtain ⟨y, rfl⟩ := hx
  refine ⟨Algebra.TensorProduct.map (AlgHom.id A A) (IntermediateField.inclusion h) y, ?_⟩
  have : (incMap κ K A L').comp (Algebra.TensorProduct.map (AlgHom.id A A) (IntermediateField.inclusion h))
      = incMap κ K A L := Algebra.TensorProduct.ext' (fun a l => by simp)
  exact congrArg (fun F : A ⊗[κ] L →ₐ[A] A ⊗[κ] K => F y) this

theorem exists_fd_range {κ K A : Type} [Field κ] [Field K] [Algebra κ K] [Algebra.IsIntegral κ K] [CommRing A]
    [Algebra κ A] (s : Finset (A ⊗[κ] K)) :
    ∃ L : IntermediateField κ K, FiniteDimensional κ L ∧ ∀ x ∈ s, x ∈ (incMap κ K A L).range := by
  have one : ∀ x : A ⊗[κ] K, ∃ L : IntermediateField κ K, FiniteDimensional κ L ∧ x ∈ (incMap κ K A L).range := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨⊥, inferInstance, zero_mem _⟩
    | tmul a k =>
      refine ⟨IntermediateField.adjoin κ {k},
        IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral k), ?_⟩
      exact ⟨a ⊗ₜ ⟨k, IntermediateField.mem_adjoin_simple_self κ k⟩, by simp⟩
    | add x y hx hy =>
      obtain ⟨L₁, h₁, hx⟩ := hx
      obtain ⟨L₂, h₂, hy⟩ := hy
      exact ⟨L₁ ⊔ L₂, inferInstance, add_mem (incMap_mono le_sup_left hx) (incMap_mono le_sup_right hy)⟩
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨⊥, inferInstance, by simp⟩
  | insert a s _ ih =>
    obtain ⟨L₁, h₁, ha⟩ := one a
    obtain ⟨L₂, h₂, hs⟩ := ih
    refine ⟨L₁ ⊔ L₂, inferInstance, ?_⟩
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact incMap_mono le_sup_left ha
    · exact incMap_mono le_sup_right (hs x hx)

theorem SHInsepHens_of (hL : SHInsepLoc) : SHInsepHens := by
  intro κ K A _ _ _ _ _ _ hA _
  have hA' := hA
  obtain ⟨_, -⟩ := hA'
  refine { toIsLocalRing := inferInstance, is_henselian := ?_ }
  intro f hf a₀ h1 h2
  classical
  obtain ⟨L, hFD, hs⟩ := exists_fd_range (A := A) (insert a₀ (f.support.image f.coeff))
  have : IsLocalRing (A ⊗[κ] L) := hL κ L A hA
  have : HenselianLocalRing (A ⊗[κ] L) := GlobalTheory.henselianLocalRing_of_finite A _
  have hint : (incMap κ K A L).toRingHom.IsIntegral := by
    refine RingHom.IsIntegral.tower_top (algebraMap A (A ⊗[κ] L)) _ ?_
    have e : (incMap κ K A L).toRingHom.comp (algebraMap A (A ⊗[κ] L)) = algebraMap A (A ⊗[κ] K) :=
      (incMap κ K A L).comp_algebraMap
    rw [e]
    exact fun x => Algebra.IsIntegral.isIntegral (R := A) x
  have hc : (maximalIdeal (A ⊗[κ] K)).comap (incMap κ K A L).toRingHom = maximalIdeal (A ⊗[κ] L) :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' _ hint _)
  refine hens_root_of_sub (incMap κ K A L).toRingHom hc f hf a₀ ?_ ?_ h1 h2
  · intro n
    by_cases hn : n ∈ f.support
    · exact (AlgHom.mem_range _).1 (hs _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hn)))
    · exact ⟨0, by simp [Polynomial.notMem_support_iff.1 hn]⟩
  · exact (AlgHom.mem_range _).1 (hs _ (Finset.mem_insert_self _ _))

end LateralTheory.KummerTheory
end
end

-- bundled from Development.EtaleCohomology.KummerTheory.SHInsepLocPf
section
noncomputable section
open scoped TensorProduct

namespace LateralTheory.KummerTheory

section
variable {κ K : Type} [Field κ] [Field K] [Algebra κ K]

theorem shl_nontriv (B : Type) [CommRing B] [Nontrivial B] [Algebra κ B] : Nontrivial (B ⊗[κ] K) :=
  TensorProduct.nontrivial_of_linearMap_injective_of_flat_right κ B K (Algebra.linearMap κ B)
    (algebraMap κ B).injective

variable [IsPurelyInseparable κ K] {A : Type} [CommRing A] [Algebra κ A]

theorem shl_pow (q : ℕ) [ExpChar κ q] [ExpChar (A ⊗[κ] K) q] (y : A ⊗[κ] K) :
    ∃ n : ℕ, ∃ a : A, y ^ q ^ n = algebraMap A (A ⊗[κ] K) a := by
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul a k =>
    obtain ⟨n, c, hc⟩ := (isPurelyInseparable_iff_pow_mem κ q).1 inferInstance k
    refine ⟨n, c • a ^ q ^ n, ?_⟩
    rw [Algebra.TensorProduct.tmul_pow, ← hc, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
      Algebra.TensorProduct.algebraMap_apply]
    simp [TensorProduct.smul_tmul']
  | add x y hx hy =>
    obtain ⟨n, a, ha⟩ := hx
    obtain ⟨m, b, hb⟩ := hy
    refine ⟨n + m, a ^ q ^ m + b ^ q ^ n, ?_⟩
    rw [add_pow_expChar_pow, map_add, map_pow, map_pow, ← ha, ← hb, ← pow_mul, ← pow_mul, ← pow_add,
      ← pow_add, add_comm m n]

end

theorem SHInsepLoc_of : SHInsepLoc := by
  intro κ K A _ _ _ _ _ _ hA
  obtain ⟨hH, _⟩ := hA
  have : IsLocalRing A := hH.toIsLocalRing
  obtain ⟨q, hq⟩ := ExpChar.exists κ
  have : Nontrivial (A ⊗[κ] K) := shl_nontriv A
  have : ExpChar (A ⊗[κ] K) q := expChar_of_injective_algebraMap (algebraMap κ _).injective q
  have hqpos : ∀ n : ℕ, q ^ n ≠ 0 := fun n => pow_ne_zero _ (expChar_pos κ q).ne'

  have hm : ∀ a ∈ IsLocalRing.maximalIdeal A, ¬ IsUnit (algebraMap A (A ⊗[κ] K) a) := by
    intro a ha hu
    have : Nontrivial ((A ⧸ IsLocalRing.maximalIdeal A) ⊗[κ] K) := shl_nontriv _
    let φ := Algebra.TensorProduct.map (Ideal.Quotient.mkₐ κ (IsLocalRing.maximalIdeal A)) (AlgHom.id κ K)
    have h0 : φ (algebraMap A (A ⊗[κ] K) a) = 0 := by
      simp [φ, Algebra.TensorProduct.algebraMap_apply, Ideal.Quotient.eq_zero_iff_mem.2 ha]
    have := hu.map φ
    rw [h0] at this
    exact not_isUnit_zero this
  have hkey : ∀ y : A ⊗[κ] K, ¬ IsUnit y →
      ∃ n : ℕ, ∃ a ∈ IsLocalRing.maximalIdeal A, y ^ q ^ n = algebraMap A (A ⊗[κ] K) a := by
    intro y hy
    obtain ⟨n, a, ha⟩ := shl_pow q y
    refine ⟨n, a, ?_, ha⟩
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact hy ((isUnit_pow_iff (hqpos n)).1 (ha ▸ hu.map _))
  refine IsLocalRing.of_nonunits_add ?_
  intro x y hx hy hxy
  obtain ⟨n, a, ha, hxa⟩ := hkey x hx
  obtain ⟨m, b, hb, hyb⟩ := hkey y hy
  apply hm (a ^ q ^ m + b ^ q ^ n)
  · exact Ideal.add_mem _ (Ideal.pow_mem_of_mem _ ha _ (Nat.pos_of_ne_zero (hqpos m)))
      (Ideal.pow_mem_of_mem _ hb _ (Nat.pos_of_ne_zero (hqpos n)))
  · have : (x + y) ^ q ^ (n + m) = algebraMap A (A ⊗[κ] K) (a ^ q ^ m + b ^ q ^ n) := by
      rw [add_pow_expChar_pow, map_add, map_pow, map_pow, ← hxa, ← hyb, ← pow_mul, ← pow_mul, ← pow_add,
        ← pow_add, add_comm m n]
    rw [← this]
    exact hxy.pow _

end LateralTheory.KummerTheory
end
end

-- bundled from Development.EtaleCohomology.KummerTheory.SHInsepResPf
section
noncomputable section
open scoped TensorProduct
open Polynomial

namespace LateralTheory.KummerTheory

section
variable (κ K A : Type) [Field κ] [Field K] [Algebra κ K] [IsPurelyInseparable κ K] [CommRing A]
  [Algebra κ A]

theorem shInsepRes_pow [Nontrivial (A ⊗[κ] K)] (y : A ⊗[κ] K) :
    ∃ n : ℕ, ∃ a : A, y ^ (ringExpChar κ) ^ n = algebraMap A (A ⊗[κ] K) a := by
  set q := ringExpChar κ
  have : ExpChar (A ⊗[κ] K) q :=
    expChar_of_injective_algebraMap (algebraMap κ (A ⊗[κ] K)).injective q
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul a k =>
    obtain ⟨n, c, hc⟩ := IsPurelyInseparable.pow_mem κ q k
    refine ⟨n, c • a ^ q ^ n, ?_⟩
    rw [Algebra.TensorProduct.tmul_pow, ← hc]
    show (a ^ q ^ n) ⊗ₜ[κ] (algebraMap κ K c) = (c • a ^ q ^ n) ⊗ₜ[κ] (1 : K)
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  | add x y hx hy =>
    obtain ⟨n, a, ha⟩ := hx
    obtain ⟨m, b, hb⟩ := hy
    refine ⟨n + m, a ^ q ^ m + b ^ q ^ n, ?_⟩
    rw [add_pow_expChar_pow, map_add, map_pow, map_pow, ← ha, ← hb, ← pow_mul, ← pow_mul, ← pow_add,
      ← pow_add, add_comm m n]

omit [IsPurelyInseparable κ K] in
theorem shInsepRes_inj : Function.Injective (algebraMap A (A ⊗[κ] K)) :=
  Algebra.TensorProduct.includeLeft_injective (S := A) (algebraMap κ K).injective

theorem shInsepRes_localHom [Nontrivial (A ⊗[κ] K)] : IsLocalHom (algebraMap A (A ⊗[κ] K)) := by
  refine ⟨fun a ha => ?_⟩
  obtain ⟨u, hu⟩ := ha
  obtain ⟨n, b, hb⟩ := shInsepRes_pow κ K A (↑u⁻¹ : A ⊗[κ] K)
  have hQ : (ringExpChar κ) ^ n ≠ 0 := pow_ne_zero _ (expChar_pos κ (ringExpChar κ)).ne'
  have h1 : algebraMap A (A ⊗[κ] K) (a ^ (ringExpChar κ) ^ n * b) = algebraMap A (A ⊗[κ] K) 1 := by
    rw [map_mul, map_pow, ← hb, ← hu, ← mul_pow, Units.mul_inv, one_pow, map_one]
  have h2 := shInsepRes_inj κ K A h1
  exact (isUnit_pow_iff hQ).mp (isUnit_of_mul_isUnit_left (h2 ▸ isUnit_one))

end

theorem SHInsepRes_of : SHInsepRes := by
  intro κ K A _ _ _ _ _ _ hA _
  obtain ⟨hh, hsc⟩ := hA
  have : IsLocalRing A := hh.toIsLocalRing
  have : IsLocalHom (algebraMap A (A ⊗[κ] K)) := shInsepRes_localHom κ K A
  let _ : Algebra (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField (A ⊗[κ] K)) :=
    (IsLocalRing.ResidueField.map (algebraMap A (A ⊗[κ] K))).toAlgebra
  have : Algebra.IsAlgebraic (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField (A ⊗[κ] K)) := by
    constructor
    intro x
    obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective x
    obtain ⟨n, a, ha⟩ := shInsepRes_pow κ K A y
    have hQ : 0 < (ringExpChar κ) ^ n := pow_pos (expChar_pos κ (ringExpChar κ)) _
    refine ⟨X ^ (ringExpChar κ) ^ n - C (IsLocalRing.residue A a), X_pow_sub_C_ne_zero hQ _, ?_⟩
    rw [map_sub, map_pow, aeval_X, aeval_C, ← map_pow, ha, sub_eq_zero]
    rfl
  exact Algebra.IsAlgebraic.isSepClosed (F := IsLocalRing.ResidueField A)

end LateralTheory.KummerTheory
end
end

-- bundled from Development.EtaleCohomology.KummerTheory.TwExtPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.TwExtPf

theorem sep {M : Shv ℤ} {U : Scheme.{0}} (x y : Sec M U)
    (h : Loc U fun V g => Sec.res g x = Sec.res g y) : x = y := by
  obtain ⟨S, hS, hP⟩ := h
  exact Sheaf.isSeparated M U S hS x y (fun V g hg => hP _ g hg)

theorem TwExt_of (hT : LateralTheory.EtaleFoundations.EtaleTateTwistSectionsLocallyGenerated) (hM : LateralTheory.EtaleFoundations.EtaleSheafMonoEpiSectionCriteria) :
    LateralTheory.KummerTheory.BockCut.TwExt := by
  intro Q _ i M φ ψ h
  refine (hM ℤ φ).2.2.2 ψ fun U a => ?_
  obtain ⟨S, hS, hP⟩ := (hT Q i).1 U a
  refine sep _ _ ⟨S, hS, fun V g hg => ?_⟩
  have nφ : Sec.res g (Sec.map φ a) = Sec.map φ (Sec.res g a) :=
    congrArg (fun f => (ModuleCat.Hom.hom f) a) (φ.hom.naturality g.op).symm
  have nψ : Sec.res g (Sec.map ψ a) = Sec.map ψ (Sec.res g a) :=
    congrArg (fun f => (ModuleCat.Hom.hom f) a) (ψ.hom.naturality g.op).symm
  show Sec.res g (Sec.map φ a) = Sec.res g (Sec.map ψ a)
  rw [nφ, nψ]
  have ha : Sec.res g a = 0 ∨ ∃ (ζ : Prim Q Γ(V, ⊤)) (c : ℕ), (Sec.res g a : Sec (LateralTheory.KummerTheory.BockCut.TZ Q i) V) = c • LateralTheory.KummerTheory.BockCut.genZ i ζ := hP V g hg
  rcases ha with h0 | ⟨ζ, c, hc⟩
  · have e : (Sec.res g a : Sec (LateralTheory.KummerTheory.BockCut.TZ Q i) V) = 0 := h0
    rw [e]; simp only [Sec.map, map_zero]
  · rw [hc]; have hh := h V ζ; simp only [Sec.map] at hh ⊢; rw [map_nsmul, map_nsmul, hh]

end LateralTheory.KummerTheory.TwExtPf
end
end

