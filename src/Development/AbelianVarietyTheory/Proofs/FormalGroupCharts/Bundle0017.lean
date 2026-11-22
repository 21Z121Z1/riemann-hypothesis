import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.TwoChartSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IsNilpotentOfMemKerJetTruncR
section
noncomputable section
open CategoryTheory AlgebraicGeometry MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
namespace GlobalTheory.JetSer

section Val
variable {A : Type} [CommRing A] {X : Scheme.{0}}

def fnValHom (p : Spec (CommRingCat.of A) ⟶ X) (U : X.Opens) (h : ⊤ ≤ p ⁻¹ᵁ U) : Γ(X, U) →+* A :=
  (p.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom).hom

theorem fnVal_eq_fnValHom (p : Spec (CommRingCat.of A) ⟶ X) (U : X.Opens) (h : ⊤ ≤ p ⁻¹ᵁ U) (f : Γ(X, U)) :
    fnVal p U f = fnValHom p U h f := by
  unfold fnVal
  rw [dif_pos h]
  rfl

theorem top_le_preimage_comp {T T' : Scheme.{0}} (r : T' ⟶ T) (p : T ⟶ X) (U : X.Opens) (h : ⊤ ≤ p ⁻¹ᵁ U) :
    ⊤ ≤ (r ≫ p) ⁻¹ᵁ U := fun z _ => by
  have : r z ∈ p ⁻¹ᵁ U := h trivial
  simpa using this

theorem fnVal_specMap {B : Type} [CommRing B] (ψ : A →+* B) (p : Spec (CommRingCat.of A) ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ p ⁻¹ᵁ U) (f : Γ(X, U)) :
    fnVal (Spec.map (CommRingCat.ofHom ψ) ≫ p) U f = ψ (fnVal p U f) := by
  have h' := top_le_preimage_comp (Spec.map (CommRingCat.ofHom ψ)) p U h
  rw [fnVal_eq_fnValHom _ _ h', fnVal_eq_fnValHom _ _ h]
  have e : (Spec.map (CommRingCat.ofHom ψ) ≫ p).appLE U ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom =
      (p.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom) ≫ CommRingCat.ofHom ψ := by
    rw [Category.assoc, ← Scheme.ΓSpecIso_naturality, ← Category.assoc,
      ← Scheme.Hom.appLE_comp_appLE (Spec.map (CommRingCat.ofHom ψ)) p U ⊤ ⊤ h le_top]
    congr 2
  unfold fnValHom
  rw [e]
  rfl

theorem fnVal_comp {Y : Scheme.{0}} (p : Spec (CommRingCat.of A) ⟶ X) (q : X ⟶ Y) (U : X.Opens) (V : Y.Opens)
    (hUV : U ≤ q ⁻¹ᵁ V) (h : ⊤ ≤ p ⁻¹ᵁ U) (f : Γ(Y, V)) :
    ⊤ ≤ (p ≫ q) ⁻¹ᵁ V ∧ fnVal (p ≫ q) V f = fnVal p U ((q.appLE V U hUV).hom f) := by
  have h' : ⊤ ≤ (p ≫ q) ⁻¹ᵁ V := fun z _ => by
    have : p z ∈ q ⁻¹ᵁ V := hUV (h trivial)
    simpa using this
  refine ⟨h', ?_⟩
  rw [fnVal_eq_fnValHom _ _ h', fnVal_eq_fnValHom _ _ h]
  unfold fnValHom
  rw [← Scheme.Hom.appLE_comp_appLE p q V U ⊤ hUV h]
  rfl

theorem fnVal_res (p : Spec (CommRingCat.of A) ⟶ X) (U V : X.Opens) (hUV : U ≤ V) (h : ⊤ ≤ p ⁻¹ᵁ U)
    (f : Γ(X, V)) :
    ⊤ ≤ p ⁻¹ᵁ V ∧ fnVal p V f = fnVal p U ((X.presheaf.map (homOfLE hUV).op).hom f) := by
  have h' : ⊤ ≤ p ⁻¹ᵁ V := fun z _ => hUV (h trivial)
  refine ⟨h', ?_⟩
  rw [fnVal_eq_fnValHom _ _ h', fnVal_eq_fnValHom _ _ h]
  unfold fnValHom
  rw [← Scheme.Hom.map_appLE p h (homOfLE hUV).op]
  rfl

theorem top_le_preimage_of_nil {B : Type} [CommRing B] (q : A →+* B) (hq : Function.Surjective q)
    (hn : ∀ a ∈ RingHom.ker q, IsNilpotent a) (p : Spec (CommRingCat.of A) ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ (Spec.map (CommRingCat.ofHom q) ≫ p) ⁻¹ᵁ U) : ⊤ ≤ p ⁻¹ᵁ U := by
  intro z _
  have hker : RingHom.ker q ≤ z.asIdeal := fun a ha => by
    obtain ⟨n, hn⟩ := hn a ha
    exact z.isPrime.mem_of_pow_mem n (by rw [hn]; exact zero_mem _)
  have := z.isPrime
  have hprime : (z.asIdeal.map q).IsPrime := Ideal.map_isPrime_of_surjective hq hker
  let z₀ : ↥(Spec (CommRingCat.of B)) := (⟨z.asIdeal.map q, hprime⟩ : PrimeSpectrum B)
  have hz : (Spec.map (CommRingCat.ofHom q)) z₀ = z := by
    apply PrimeSpectrum.ext
    change Ideal.comap q (Ideal.map q z.asIdeal) = z.asIdeal
    rw [Ideal.comap_map_of_surjective' q hq, sup_eq_left.mpr hker]
  have h0 : z₀ ∈ (Spec.map (CommRingCat.ofHom q) ≫ p) ⁻¹ᵁ U := h trivial
  rw [← hz]
  simpa using h0

end Val

section Jet
variable {R : Type} [CommRing R] {κ : Type}

theorem jetTruncR_surjective (m : ℕ) : Function.Surjective (jetTruncR R κ m) := by
  intro y
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨Ideal.Quotient.mk _ a, rfl⟩

theorem isNilpotent_of_mem_ker_jetTruncR (m : ℕ) (a : JetR R κ (m + 1))
    (ha : a ∈ RingHom.ker (jetTruncR R κ m).toRingHom) : IsNilpotent a := by
  have e : (jetAug R κ m).comp (jetTruncR R κ m) = jetAug R κ (m + 1) :=
    jet_ext fun j => (jetAug_zR m j).trans (jetAug_zR (m + 1) j).symm
  have ha' : jetTruncR R κ m a = 0 := ha
  have h1 : a ∈ RingHom.ker (jetAug R κ (m + 1)) := by
    rw [RingHom.mem_ker, ← e, AlgHom.comp_apply, ha', map_zero]
  refine ⟨m + 1 + 1, ?_⟩
  have := Ideal.pow_mem_pow h1 (m + 1 + 1)
  rwa [ker_jetAug_pow, Ideal.mem_bot] at this

theorem top_le_preimage_jet {X : Scheme.{0}} (p : ∀ m : ℕ, Spec (CommRingCat.of (JetR R κ m)) ⟶ X)
    (hp : ∀ m, (spMap (jetTruncR R κ m)).left ≫ p (m + 1) = p m) (U : X.Opens) (h : ⊤ ≤ p 0 ⁻¹ᵁ U) (m : ℕ) :
    ⊤ ≤ p m ⁻¹ᵁ U := by
  induction m with
  | zero => exact h
  | succ m ih =>
    rw [← hp m] at ih
    exact top_le_preimage_of_nil (jetTruncR R κ m).toRingHom (jetTruncR_surjective m)
      (isNilpotent_of_mem_ker_jetTruncR m) _ U ih

end Jet

theorem serSt_of_jetAlgSt : JetAlgSt → SerSt := by
  intro hJ R _ κ _ X p hp U h0
  have hU := top_le_preimage_jet p hp U h0
  obtain ⟨hτ, -, hinj, hex, -⟩ := hJ R κ
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hc : ∀ f : Γ(X, U), ∃ g : MvPowerSeries κ R, ∀ m, toJet m g = fnValHom (p m) U (hU m) f := by
      intro f
      refine hex (fun m => fnValHom (p m) U (hU m) f) fun m => ?_
      have := fnVal_specMap (jetTruncR R κ m).toRingHom (p (m + 1)) U (hU _) f
      rw [← spMap_left, hp m, fnVal_eq_fnValHom _ _ (hU _), fnVal_eq_fnValHom _ _ (hU _)] at this
      exact this.symm
    choose T hT using hc
    choose τ hτ₁ hτ₂ using hτ
    refine ⟨{ toFun := T
              map_one' := hinj _ _ fun m => by rw [hT, ← hτ₁, map_one, map_one]
              map_mul' := fun a b => hinj _ _ fun m => by
                rw [hT, ← hτ₁, map_mul, map_mul, hτ₁, hτ₁, hT, hT]
              map_zero' := hinj _ _ fun m => by rw [hT, ← hτ₁, map_zero, map_zero]
              map_add' := fun a b => hinj _ _ fun m => by
                rw [hT, ← hτ₁, map_add, map_add, hτ₁, hτ₁, hT, hT] }, fun f g => ⟨fun H => ?_, fun H m => ?_⟩⟩
    · exact hinj _ _ fun m => by
        rw [← (H m).2, fnVal_eq_fnValHom _ _ (hU m)]
        exact (hT f m).symm
    · refine ⟨hU m, ?_⟩
      rw [H, fnVal_eq_fnValHom _ _ (hU m)]
      exact (hT f m).symm
  · intro V h f g
    refine forall_congr' fun m => ?_
    obtain ⟨h1, h2⟩ := fnVal_res (p m) U V h (hU m) f
    rw [h2]
    exact ⟨fun H => ⟨hU m, H.2⟩, fun H => ⟨h1, H.2⟩⟩
  · intro Y q V h f g
    refine forall_congr' fun m => ?_
    obtain ⟨h1, h2⟩ := fnVal_comp (p m) q U V h (hU m) f
    rw [h2]
    exact ⟨fun H => ⟨hU m, H.2⟩, fun H => ⟨h1, H.2⟩⟩
  · intro κ' _ b ψ hb hψ f g H m
    refine ⟨top_le_preimage_comp _ _ U (hU m), ?_⟩
    have := fnVal_specMap (ψ m).toRingHom (p m) U (hU m) f
    rw [(H m).2] at this
    exact this.trans (((hJ R κ').2.2.2.2 κ b hb m).2 (ψ m) (hψ m) g)

end GlobalTheory.JetSer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IsUniversalChartOfFormalGroupChart
section
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChartUniv

section Jets
open ReciprocityTheory.ChartRestriction.G.Chart

variable {R : Type} [CommRing R]

theorem jetAug_eq (κ : Type) (m : ℕ) : jetAug R κ m = (jetAug R κ 0).comp (jetZeroR R κ m) :=
  jet_ext fun j => by rw [AlgHom.comp_apply, jetAug_zR]; exact (jetAug_zR (R := R) 0 j).symm

theorem jetZero_zR (κ : Type) (m : ℕ) (j : κ) : jetZeroR R κ m (zR m j) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.2 (by rw [zero_add, pow_one]; exact Ideal.subset_span ⟨j, rfl⟩)

theorem jetZero_eq (κ : Type) (m : ℕ) : jetZeroR R κ m = (Algebra.ofId R (JetR R κ 0)).comp (jetAug R κ m) :=
  jet_ext fun j => by rw [AlgHom.comp_apply, jetAug_zR, map_zero, jetZero_zR]

theorem aug_comp_iff {κ κ' : Type} {m : ℕ} (ψ : JetR R κ m →ₐ[R] JetR R κ' m) :
    (jetAug R κ' m).comp ψ = jetAug R κ m ↔ ∀ j, jetZeroR R κ' m (ψ (zR m j)) = 0 := by
  constructor
  · intro h j
    have := AlgHom.congr_fun h (zR m j)
    rw [AlgHom.comp_apply, jetAug_zR] at this
    rw [jetZero_eq, AlgHom.comp_apply, this, map_zero]
  · intro h
    refine jet_ext fun j => ?_
    rw [AlgHom.comp_apply, jetAug_zR, jetAug_eq, AlgHom.comp_apply, h, map_zero]

theorem spMap_id' (A : Type) [CommRing A] [Algebra R A] : spMap (R₀ := R) (AlgHom.id R A) = 𝟙 _ := by
  apply Over.OverMorphism.ext
  rw [spMap_left]
  exact Spec.map_id _

def jetRen {κ κ' : Type} (f : κ → κ') (m : ℕ) : JetR R κ m →ₐ[R] JetR R κ' m :=
  jetLift R (RingHom.ker (jetAug R κ' m)) (ker_jetAug_pow κ' m) (fun j => zR m (f j)) (fun j => zR_mem_ker m (f j))

theorem jetRen_zR {κ κ' : Type} (f : κ → κ') (m : ℕ) (j : κ) : jetRen (R := R) f m (zR m j) = zR m (f j) :=
  jetLift_zR _ _ _ _ j

variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G]

theorem univ_all [IsLocalRing R] [Smooth G.hom] {κ : Type} {m : ℕ} (x : sp (R₀ := R) (JetR R κ m) ⟶ G)
    (h0 : spMap (jetZeroR R κ m) ≫ x = 1)
    (hu : ∀ (κ' : Type) (y : sp (R₀ := R) (JetR R κ' m) ⟶ G), spMap (jetZeroR R κ' m) ≫ y = 1 →
      ∃! ψ : JetR R κ m →ₐ[R] JetR R κ' m, (∀ j, jetZeroR R κ' m (ψ (zR m j)) = 0) ∧ y = spMap ψ ≫ x)
    (A : Type) [CommRing A] [Algebra R A] (aug : A →ₐ[R] R) (hA : (RingHom.ker aug) ^ (m + 1) = ⊥)
    (y : sp (R₀ := R) A ⟶ G) (hy : spMap aug ≫ y = 1) :
    ∃! ψ : JetR R κ m →ₐ[R] A, aug.comp ψ = jetAug R κ m ∧ y = spMap ψ ≫ x := by
  obtain ⟨n, z, -, hz0, hzu⟩ := univChartLoc G
  have hxa : spMap (jetAug R κ m) ≫ x = 1 := by
    rw [jetAug_eq, ← spMap_comp, Category.assoc, h0, comp_one']
  obtain ⟨α, ⟨ha1, ha2⟩, -⟩ := hzu (JetR R κ m) (jetAug R κ m) m (ker_jetAug_pow κ m) x hxa
  obtain ⟨β, ⟨hb1, hb2⟩, -⟩ := hu (Fin n) (z m) (hz0 m)
  have hb1' := (aug_comp_iff β).2 hb1
  have hab : α.comp β = AlgHom.id R _ := by
    refine (hu κ x h0).unique ⟨(aug_comp_iff _).1 ?_, ?_⟩ ⟨fun j => jetZero_zR κ m j, ?_⟩
    · rw [← AlgHom.comp_assoc, ha1, hb1']
    · rw [← spMap_comp, Category.assoc, ← hb2, ← ha2]
    · rw [spMap_id', Category.id_comp]
  obtain ⟨ψ, ⟨h1, h2⟩, hψ⟩ := hzu A aug m hA y hy
  refine ⟨ψ.comp β, ⟨?_, ?_⟩, ?_⟩
  · rw [← AlgHom.comp_assoc, h1, hb1']
  · rw [← spMap_comp, Category.assoc, ← hb2, ← h2]
  · rintro φ ⟨g1, g2⟩
    have : φ.comp α = ψ := hψ _ ⟨by rw [← AlgHom.comp_assoc, g1, ha1], by
      rw [← spMap_comp, Category.assoc, ← ha2, ← g2]⟩
    rw [← this, AlgHom.comp_assoc, hab, AlgHom.comp_id]

theorem isUnivChart_ren [IsLocalRing R] [Smooth G.hom] {κ : Type} {d : ℕ} (e : κ ≃ Fin d)
    (x : ∀ m, sp (R₀ := R) (JetR R κ m) ⟶ G)
    (ht : ∀ m, spMap (jetTruncR R κ m) ≫ x (m + 1) = x m)
    (h0 : ∀ m, spMap (jetZeroR R κ m) ≫ x m = 1)
    (hu : ∀ (κ' : Type) (m : ℕ) (y : sp (R₀ := R) (JetR R κ' m) ⟶ G), spMap (jetZeroR R κ' m) ≫ y = 1 →
      ∃! ψ : JetR R κ m →ₐ[R] JetR R κ' m, (∀ j, jetZeroR R κ' m (ψ (zR m j)) = 0) ∧ y = spMap ψ ≫ x m) :
    IsUnivChart G d (fun m => spMap (jetRen e m) ≫ x m) := by
  refine ⟨fun m => ?_, fun m => ?_, fun A _ _ aug m hA y hy => ?_⟩
  · have : (jetTruncR R (Fin d) m).comp (jetRen e (m + 1)) = (jetRen e m).comp (jetTruncR R κ m) :=
      jet_ext fun j => by
        rw [AlgHom.comp_apply, AlgHom.comp_apply, jetRen_zR]
        exact (jetRen_zR (R := R) e m j).symm
    show _ ≫ _ ≫ _ = _ ≫ _
    rw [← Category.assoc, spMap_comp, this, ← spMap_comp, Category.assoc, ht]
  · have : (jetZeroR R (Fin d) m).comp (jetRen e m) = (jetRen e 0).comp (jetZeroR R κ m) :=
      jet_ext fun j => by
        rw [AlgHom.comp_apply, AlgHom.comp_apply, jetRen_zR, jetZero_zR, jetZero_zR, map_zero]
    show _ ≫ _ ≫ _ = _
    rw [← Category.assoc, spMap_comp, this, ← spMap_comp, Category.assoc, h0, comp_one']
  · obtain ⟨ψ, ⟨h1, h2⟩, hψ⟩ := univ_all (x m) (h0 m) (fun κ' => hu κ' m) A aug hA y hy
    have e1 : (jetRen (R := R) e m).comp (jetRen e.symm m) = AlgHom.id R _ :=
      jet_ext fun j => by rw [AlgHom.comp_apply, jetRen_zR, jetRen_zR, e.apply_symm_apply]; rfl
    have e2 : (jetRen (R := R) e.symm m).comp (jetRen e m) = AlgHom.id R _ :=
      jet_ext fun j => by rw [AlgHom.comp_apply, jetRen_zR, jetRen_zR, e.symm_apply_apply]; rfl
    have a1 : (jetAug R κ m).comp (jetRen e.symm m) = jetAug R (Fin d) m :=
      jet_ext fun j => by rw [AlgHom.comp_apply, jetRen_zR, jetAug_zR, jetAug_zR]
    have a2 : (jetAug R (Fin d) m).comp (jetRen e m) = jetAug R κ m :=
      jet_ext fun j => by rw [AlgHom.comp_apply, jetRen_zR, jetAug_zR, jetAug_zR]
    refine ⟨ψ.comp (jetRen e.symm m), ⟨?_, ?_⟩, ?_⟩
    · rw [← AlgHom.comp_assoc, h1, a1]
    · show y = _ ≫ _ ≫ _
      rw [← Category.assoc, spMap_comp, AlgHom.comp_assoc, e2, AlgHom.comp_id]
      exact h2
    · rintro φ ⟨g1, g2⟩
      have : φ.comp (jetRen e m) = ψ := hψ _ ⟨by rw [← AlgHom.comp_assoc, g1, a2], by
        rw [← spMap_comp, Category.assoc]; exact g2⟩
      rw [← this, AlgHom.comp_assoc, e1, AlgHom.comp_id]

end Jets

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
open scoped CategoryTheory.Obj

theorem isUnivChart_of_isChartJ : ∀ (T : Type) [CommRing T] [IsLocalRing T] (G : Over (Sp T)) [GrpObj G] [IsCommMonObj G], Smooth G.hom → ∀ (d : ℕ) (F : FGLaw T d) (x : ∀ m : ℕ, algOver T (JetR T (Fin 1 × Fin d) m) ⟶ G), IsChartJ G F x → ∃ x0 : GlobalTheory.JetSer.Fam G (Fin d), Chart.IsUnivChart G d x0 ∧ ∃ ρ : ∀ m, JetR T (Fin 1 × Fin d) m →ₐ[T] Chart.JetR T (Fin d) m, (∀ m j, ρ m (zR m ((0 : Fin 1), j)) = Chart.zR m j) ∧ ∀ m, (x0 m).left = spMap (ρ m : JetR T (Fin 1 × Fin d) m →+* Chart.JetR T (Fin d) m) ≫ (x m).left := by
  intro T _ _ G _ _ hG d F x hx
  haveI := hG
  let e : Fin 1 × Fin d ≃ Fin d := Equiv.uniqueProd (Fin d) (Fin 1)
  refine ⟨fun m => Chart.spMap (jetRen e m) ≫ x m,
    isUnivChart_ren e x hx.trunc hx.zero hx.univ, fun m => jetRen e m, fun m j => jetRen_zR e m _, fun m => rfl⟩

end GlobalTheory.ChartUniv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.RepJetAugCompTrunc
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.JetSer
variable {R : Type} [CommRing R]

theorem rep_jetAug_comp_trunc (κ : Type) (m : ℕ) :
    (jetAug R κ m).comp (jetTruncR R κ m) = jetAug R κ (m + 1) :=
  jet_ext fun j => (jetAug_zR m j).trans (jetAug_zR (m + 1) j).symm

theorem rep_jetAug_comp_zero (κ : Type) (m : ℕ) :
    (jetAug R κ 0).comp (jetZeroR R κ m) = jetAug R κ m :=
  jet_ext fun j => (jetAug_zR 0 j).trans (jetAug_zR m j).symm

theorem isFPt_of_isUnivChart {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {d : ℕ} {x : Fam G (Fin d)}
    (hx : IsUnivChart G d x) : IsFPt x := by
  refine ⟨hx.1, fun m => ?_⟩
  rw [← rep_jetAug_comp_zero, ← spMap_comp, Category.assoc, hx.2.1 m]
  exact MonObj.comp_one _

theorem repSt_of_jetAlgSt (hJ : JetAlgSt) : RepSt := by
  intro R _ G _ d x hx κ _
  obtain ⟨hτ, htr, hinj, hsur, hsub⟩ := hJ R κ
  have hxa := (isFPt_of_isUnivChart hx).2
  have haug : ∀ (a : Fin d → MvPowerSeries κ R), (∀ j, constantCoeff (a j) = 0) → ∀ m
      (ψ : JetR R (Fin d) m →ₐ[R] JetR R κ m), (∀ j, ψ (zR m j) = toJet m (a j)) →
      (jetAug R κ m).comp ψ = jetAug R (Fin d) m := by
    intro a ha m ψ hψ
    refine jet_ext fun j => ?_
    rw [AlgHom.comp_apply, hψ, (htr m _).2, ha, jetAug_zR]
  have hfp : ∀ a (y : Fam G κ), Rep x a y → IsFPt y := by
    rintro a y ⟨ha, hy⟩
    choose ψ hψ hy using hy
    refine ⟨fun m => ?_, fun m => ?_⟩
    · have e : (jetTruncR R κ m).comp (ψ (m + 1)) = (ψ m).comp (jetTruncR R (Fin d) m) := by
        refine jet_ext fun j => ?_
        rw [AlgHom.comp_apply, hψ, (htr m _).1]
        exact (hψ m j).symm
      rw [hy, hy, ← Category.assoc, spMap_comp, e, ← spMap_comp, Category.assoc, hx.1]
    · rw [hy, ← Category.assoc, spMap_comp, haug a ha m _ (hψ m), hxa]
  refine ⟨fun a ha => ?_, fun y hy => ?_, hfp, ⟨fun j => by simp, fun m => ?_⟩, ?_⟩
  · choose ψ hψ using fun m => (hsub (Fin d) a ha m).1
    refine ⟨fun m => spMap (ψ m) ≫ x m, ⟨ha, fun m => ⟨ψ m, hψ m, rfl⟩⟩, ?_⟩
    rintro y ⟨-, hy⟩
    funext m
    obtain ⟨ψ', h1, h2⟩ := hy m
    have : ψ' = ψ m := jet_ext fun j => (h1 j).trans (hψ m j).symm
    rw [h2, this]
  · have hU := fun m => hx.2.2 (JetR R κ m) (jetAug R κ m) m (ker_jetAug_pow κ m) (y m) (hy.2 m)
    choose ψ hψ hu using hU
    have hc : ∀ m, (jetTruncR R κ m).comp (ψ (m + 1)) = (ψ m).comp (jetTruncR R (Fin d) m) := by
      intro m
      have hk : RingHom.ker (jetAug R κ m) ^ (m + 1 + 1) = ⊥ := by
        rw [pow_succ (RingHom.ker (jetAug R κ m)) (m + 1), ker_jetAug_pow, Ideal.bot_mul]
      refine (hx.2.2 (JetR R κ m) (jetAug R κ m) (m + 1) hk (y m) (hy.2 m)).unique ⟨?_, ?_⟩ ⟨?_, ?_⟩
      · rw [← AlgHom.comp_assoc, rep_jetAug_comp_trunc, (hψ (m + 1)).1]
      · rw [← spMap_comp, Category.assoc, ← (hψ (m + 1)).2, hy.1 m]
      · rw [← AlgHom.comp_assoc, (hψ m).1, rep_jetAug_comp_trunc]
      · rw [← spMap_comp, Category.assoc, hx.1 m, ← (hψ m).2]
    have hex : ∀ j, ∃ g : MvPowerSeries κ R, ∀ m, toJet m g = ψ m (zR m j) := fun j =>
      hsur (fun m => ψ m (zR m j)) (fun m => AlgHom.congr_fun (hc m) (zR (m + 1) j))
    choose a ha using hex
    refine ⟨a, ⟨fun j => ?_, fun m => ⟨ψ m, fun j => (ha j m).symm, (hψ m).2⟩⟩, ?_⟩
    · rw [← (htr 0 _).2, ha, ← jetAug_zR (R := R) 0 j]
      exact AlgHom.congr_fun (hψ 0).1 _
    · rintro a' ⟨ha', hy'⟩
      funext j
      refine hinj _ _ fun m => ?_
      obtain ⟨ψ', h1, h2⟩ := hy' m
      rw [ha, ← h1, hu m ψ' ⟨haug a' ha' m ψ' h1, h2⟩]
  · refine ⟨(Algebra.ofId R _).comp (jetAug R (Fin d) m), fun j => ?_, ?_⟩
    · obtain ⟨τ, h, -⟩ := hτ m
      rw [AlgHom.comp_apply, jetAug_zR, map_zero, Pi.zero_apply, ← h, map_zero]
    · rw [← spMap_comp, Category.assoc, hxa]
      exact (MonObj.comp_one _).symm
  · rintro κ' _ b ψ hb hψ a y ⟨ha, hy⟩
    obtain ⟨-, htr', -, -, hsub'⟩ := hJ R κ'
    have hs := fun m => (hsub' κ b hb m).2 (ψ m) (hψ m)
    refine ⟨fun j => ?_, fun m => ?_⟩
    · have e : (jetAug R κ' 0).comp (ψ 0) = jetAug R κ 0 := by
        refine jet_ext fun i => ?_
        rw [AlgHom.comp_apply, hψ, (htr' 0 _).2, hb, jetAug_zR]
      rw [← (htr' 0 _).2, ← hs, ← ha j, ← (htr 0 _).2]
      exact AlgHom.congr_fun e _
    · obtain ⟨φ, h1, h2⟩ := hy m
      refine ⟨(ψ m).comp φ, fun j => ?_, ?_⟩
      · rw [AlgHom.comp_apply, h1, hs]
      · show spMap (ψ m) ≫ y m = _
        rw [h2, ← Category.assoc, spMap_comp]

end GlobalTheory.JetSer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ToJetOneEqSum
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.JetSer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.JetMap

theorem isFPt_comp {R : Type} [CommRing R] {G G' : Over (Spec (CommRingCat.of R))} [GrpObj G] [GrpObj G']
    {κ : Type} {y : Fam G κ} (hy : IsFPt y) (f : G ⟶ G') (hf : η[G] ≫ f = η[G']) :
    IsFPt (fun m => y m ≫ f : Fam G' κ) := by
  refine ⟨fun m => ?_, fun m => ?_⟩
  · show spMap _ ≫ y (m + 1) ≫ f = y m ≫ f
    rw [← Category.assoc, hy.1 m]
  · show spMap _ ≫ y m ≫ f = 1
    rw [← Category.assoc, hy.2 m, Hom.one_def, Hom.one_def, Category.assoc, hf]

theorem mapSt (hJ : JetAlgSt) (hR : RepSt) : MapSt := by
  intro R _ G _ G' _ d x x' hx hx' f hf
  obtain ⟨hex, -, hfp, -, hsub⟩ := hR R G d x hx (Fin 1 × Fin d)
  obtain ⟨-, hco', -, -, hsub'⟩ := hR R G' d x' hx' (Fin 1 × Fin d)
  obtain ⟨y₀, hy₀, -⟩ := hex (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt R (n := 1) d 0) (gp_pt 0)
  obtain ⟨φ, hφ, hu⟩ := hco' _ (isFPt_comp (hfp _ _ hy₀) f hf)
  refine ⟨φ, ⟨hφ.1, fun n a y hy => ?_⟩, fun φ' hφ' => ?_⟩
  · have hb : ∀ p : Fin 1 × Fin d, constantCoeff ((![a] : Fin 1 → Pt R n d) p.1 p.2) = 0 :=
      fun p => single_point_zero_constant (a := a) hy.1 p.1 p.2
    have hψ := fun m => ((hJ R (Fin n × Fin d)).2.2.2.2 (Fin 1 × Fin d) _ hb m).1
    choose ψ hψ using hψ
    have h1 := hsub (Fin n × Fin d) _ ψ hb hψ _ _ hy₀
    have h2 := hsub' (Fin n × Fin d) _ ψ hb hψ _ _ hφ
    have h1' : Rep x a (fun m => spMap (ψ m) ≫ y₀ m) := by
      have := gt_comp1_pt a hy.1
      rw [← this]
      exact h1
    have e : y = fun m => spMap (ψ m) ≫ y₀ m :=
      ((hR R G d x hx (Fin n × Fin d)).1 a hy.1).unique hy h1'
    subst e
    simp only [Category.assoc]
    exact h2
  · have := hφ'.2 1 _ _ hy₀
    rw [gt_comp1_pt_right] at this
    exact hu _ this

theorem toJet_one_eq_sum {R : Type} [CommRing R] {κ : Type} [Fintype κ] (g : MvPowerSeries κ R)
    (hg : constantCoeff g = 0) :
    toJet 1 g = ∑ p, coeff (Finsupp.single p 1) g • zR (R := R) 1 p := by
  classical
  have h : truncTotal (1 + 1) g = ∑ p, coeff (Finsupp.single p 1) g • (MvPolynomial.X p : MvPolynomial κ R) := by
    ext e
    rw [coeff_truncTotal_eq_ite, MvPolynomial.coeff_sum]
    simp only [MvPolynomial.coeff_smul, MvPolynomial.coeff_X', smul_eq_mul, mul_ite, _root_.mul_one, mul_zero]
    by_cases he : ∃ p, Finsupp.single p 1 = e
    · obtain ⟨p, rfl⟩ := he
      rw [if_pos (by simp), Finset.sum_eq_single p (fun q _ hq => if_neg fun h =>
        hq (Finsupp.single_left_injective one_ne_zero h)) (by simp), if_pos rfl]
    · rw [Finset.sum_eq_zero fun p _ => if_neg fun h => he ⟨p, h⟩]
      split_ifs with hd
      · have h0 : e.degree = 0 := by
          by_contra h0
          have h1 : e.degree = 1 := by omega
          have : e ∈ Set.range (fun a : κ => Finsupp.single a 1) := by
            rw [Finsupp.range_single_one]; exact h1
          exact he this
        rw [(Finsupp.degree_eq_zero_iff e).1 h0]
        simpa using hg
      · rfl
  unfold toJet
  rw [h]
  exact (map_sum (Ideal.Quotient.mkₐ R _) _ _).trans
    (Finset.sum_congr rfl fun p _ => map_smul (Ideal.Quotient.mkₐ R _) _ _)

theorem dLinSt (hR : RepSt) : DLinSt := by
  intro R _ G _ G' _ d x x' hx hx' f φ hφ w hw hw'
  obtain ⟨y₀, hy₀, -⟩ := (hR R G d x hx (Fin 1 × Fin d)).1
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt R (n := 1) d 0) (gp_pt 0)
  have h' := hφ.2 1 _ _ hy₀
  rw [gt_comp1_pt_right] at h'
  obtain ⟨ψ₀, hψ₀, e₀⟩ := hy₀.2 1
  obtain ⟨ψ', hψ', e'⟩ := h'.2 1
  set c := tcoord hx w hw with hc
  let l : JetR R (Fin 1 × Fin d) 1 →ₐ[R] DualNumber R :=
    jetLift R (RingHom.ker (fstD R)) kerD_sq (fun p => TrivSqZeroExt.inr (c p.2)) (fun _ => inr_mem_kerD _)
  have hl : ∀ p, l (zR 1 p) = TrivSqZeroExt.inr (c p.2) := fun p => jetLift_zR _ _ _ _ p
  have e1 : l.comp ψ₀ = dualLift c := jet_ext fun j => by
    rw [AlgHom.comp_apply, hψ₀, dualLift_zR]
    exact (congrArg l (toJet_X 1 _)).trans (hl _)
  have e2 : l.comp ψ' = dualLift ((dLin φ).mulVec c) := jet_ext fun j => by
    rw [AlgHom.comp_apply, hψ', dualLift_zR, toJet_one_eq_sum _ (hφ.1 j), map_sum]
    simp only [map_smul, hl, ← TrivSqZeroExt.inr_smul, smul_eq_mul]
    rw [← TrivSqZeroExt.inr_sum, Fintype.sum_prod_type, Fin.sum_univ_one]
    rfl
  apply tcoord_eq
  have e'' : y₀ 1 ≫ f = spMap ψ' ≫ x' 1 := e'
  rw [← e2, ← spMap_comp, Category.assoc, ← e'', e₀, ← Category.assoc, ← Category.assoc, spMap_comp, e1,
    ← tcoord_spec hx w hw]

theorem mapSt_and_dLinSt : JetAlgSt → RepSt → MapSt ∧ DLinSt :=
  fun hJ hR => ⟨mapSt hJ hR, dLinSt hR⟩

end GlobalTheory.JetMap
end
end

