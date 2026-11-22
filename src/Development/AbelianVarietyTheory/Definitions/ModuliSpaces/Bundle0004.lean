import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0002
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.MulLeftCompOfPullbackPointEquivMul
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0003
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0130
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0152
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0135
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0124
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0109
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0092
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0008
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Statements.HeckeInFamilies.GenericMemChart
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProperZeroTriple
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LinCombTrivG
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TestObj
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.NotGoodClassZeroSucc

-- bundled from Development.AbelianVarietyTheory.Definitions.ModuliSpaces.DenseGenericOfFlat
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
namespace GlobalTheory.ZM
open GlobalTheory.SiegelRingChange GlobalTheory.SiegelPullComp

variable {o : Type} [CommRing o] {S : Scheme.{0}} {g h k : ℕ} {J : Type} {b : TBase o k} {s : S ⟶ Sp o}

theorem dense_generic_of_flat [IsDomain o] (s : S ⟶ Sp o) [Flat s] : Dense {x : S | (s x).asIdeal = ⊥} := by
  intro x
  obtain ⟨y, hy⟩ := S.affineCover.covers x
  have hcomp : Flat (S.affineCover.f (S.affineCover.idx x) ≫ s) :=
    MorphismProperty.comp_mem _ _ _ inferInstance ‹Flat s›
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (S.affineCover.f (S.affineCover.idx x) ≫ s)
  have hfl : φ.hom.Flat := by
    rw [← HasRingHomProperty.Spec_iff (P := @Flat), hφ]
    exact hcomp
  have hsp : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum o) ⤳ PrimeSpectrum.comap φ.hom y :=
    (PrimeSpectrum.le_iff_specializes _ _).1 (show (⊥ : Ideal o) ≤ _ from bot_le)
  obtain ⟨y', hy'1, hy'2⟩ := RingHom.Flat.generalizingMap_comap hfl hsp
  have hφy := congrArg (fun m => (m y').asIdeal) hφ
  have hmem : S.affineCover.f (S.affineCover.idx x) y' ∈ {x : S | (s x).asIdeal = ⊥} := by
    change ((S.affineCover.f (S.affineCover.idx x) ≫ s) y').asIdeal = ⊥
    refine Eq.trans ?_ (congrArg PrimeSpectrum.asIdeal hy'2)
    exact hφy.symm
  have h₁ : S.affineCover.f (S.affineCover.idx x) y' ⤳ S.affineCover.f (S.affineCover.idx x) y :=
    hy'1.map (S.affineCover.f (S.affineCover.idx x)).continuous
  have h₂ : S.affineCover.f (S.affineCover.idx x) y ⤳ x := by rw [hy]
  exact (h₁.trans h₂).mem_closed isClosed_closure (subset_closure hmem)

theorem dense_generic_spMap {O : Type} [CommRing O] [IsDomain O] (β : o →+* O) (hβ : Function.Injective β) :
    Dense {x : Sp O | (spMap β x).asIdeal = ⊥} := by
  intro x
  have hη : (show ↥(Sp O) from (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum O)) ⤳ x :=
    (PrimeSpectrum.le_iff_specializes _ _).1 (show (⊥ : Ideal O) ≤ x.asIdeal from bot_le)
  refine hη.mem_closed isClosed_closure (subset_closure ?_)
  change (PrimeSpectrum.comap β ⟨⊥, Ideal.isPrime_bot⟩).asIdeal = ⊥
  exact Ideal.comap_bot_of_injective β hβ

namespace SFam
variable {ζ : o}

theorem hom_ext (F : SFam h k ζ) {s' : S ⟶ Sp o} (c : SiegPre h k ζ s') (f f' : S ⟶ F.X)
    (hs : f ≫ F.s = f' ≫ F.s) (h₁ : SiegPB c F.univ f) (h₂ : SiegPB c F.univ f') : f = f' := by
  apply hom_ext_of_fromSpecStalk
  intro x
  obtain ⟨c', hc'⟩ := (siegPre_pullback h k o ζ S (Spec (S.presheaf.stalk x)) s' (S.fromSpecStalk x ≫ s')
    (S.fromSpecStalk x) c rfl).1
  exact F.inj (S.presheaf.stalk x) _ _ _ c' (by simp only [Category.assoc, hs]) (pb_comp h₁ hc') (pb_comp h₂ hc')

theorem existsUnique (F : SFam h k ζ) {s' : S ⟶ Sp o} (c : SiegPre h k ζ s') (hr : IsReduced S)
    (hd : Dense {x : S | (s' x).asIdeal = ⊥}) (hc : c.Principal) :
    ∃! f : S ⟶ F.X, f ≫ F.s = s' ∧ SiegPB c F.univ f := by
  obtain ⟨f, hf, hpb⟩ := F.rep S s' c hr hd hc
  exact ⟨f, ⟨hf, hpb⟩, fun f' hf' => F.hom_ext c f' f (hf'.1.trans hf.symm) hf'.2 hpb⟩

theorem exists_point (F : SFam h k ζ) {O : Type} [CommRing O] [IsDomain O] (β : o →+* O) (hβ : Function.Injective β)
    (c : SiegPre h k ζ (spMap β)) (hc : c.Principal) : ∃ x : Sp O ⟶ F.X, x ≫ F.s = spMap β ∧ SiegPB c F.univ x := by
  obtain ⟨f, hf, hpb⟩ := F.rep (Sp O) (spMap β) c inferInstance (dense_generic_spMap β hβ) hc
  exact ⟨f, hf, hpb⟩

theorem nonempty (F : SFam h k ζ) {O : Type} [CommRing O] [IsDomain O] (β : o →+* O) (hβ : Function.Injective β)
    (c : SiegPre h k ζ (spMap β)) (hc : c.Principal) : Nonempty F.X := by
  obtain ⟨x, -, -⟩ := F.exists_point β hβ c hc
  exact ⟨x (show ↥(Sp O) from (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum O))⟩

theorem isReduced_and_dense [IsDomain o] (F : SFam h k ζ) : IsReduced F.X ∧ Dense {x : F.X | (F.s x).asIdeal = ⊥} := by
  have := F.smooth
  have : Smooth F.s := SmoothOfRelativeDimension.smooth (n := h * (h + 1) / 2) (f := F.s)
  have : IsReduced F.X := isReduced_of_smooth_of_isReduced F.s
  exact ⟨inferInstance, dense_generic_of_flat F.s⟩

theorem exists_iso [IsDomain o] (F F' : SFam h k ζ) :
    ∃ e : F.X ≅ F'.X, e.hom ≫ F'.s = F.s ∧ SiegPB F.univ F'.univ e.hom := by
  obtain ⟨hr, hd⟩ := F.isReduced_and_dense
  obtain ⟨hr', hd'⟩ := F'.isReduced_and_dense
  obtain ⟨f, hf, hpf⟩ := F'.rep F.X F.s F.univ hr hd F.princ
  obtain ⟨g, hg, hpg⟩ := F.rep F'.X F'.s F'.univ hr' hd' F'.princ
  have e₁ : f ≫ g = 𝟙 _ :=
    F.hom_ext F.univ _ _ (by rw [Category.assoc, hg, hf, Category.id_comp]) (pb_comp hpg hpf) (pb_id _)
  have e₂ : g ≫ f = 𝟙 _ :=
    F'.hom_ext F'.univ _ _ (by rw [Category.assoc, hf, hg, Category.id_comp]) (pb_comp hpf hpg) (pb_id _)
  exact ⟨⟨f, g, e₁, e₂⟩, hf, hpf⟩

theorem exists_baseChange (F : SFam h k ζ) {B : Type} [CommRing B] {ζ' : B} (j : o →+* B) (hi : Function.Injective j)
    (hj : j ζ = ζ') : ∃ (F' : SFam h k ζ') (π : F'.X ⟶ F.X),
      IsPullback π F'.s F.s (spMap j) ∧ SiegPB F'.univ F.univ π := by
  have sq := IsPullback.of_hasPullback F.s (spMap j)
  have hrc := siegPre_pull_ringChange h k o B ζ ζ' j F.X (pullback F.s (spMap j)) F.s
    (pullback.snd F.s (spMap j)) (pullback.fst F.s (spMap j)) hj pullback.condition
  obtain ⟨u, hu⟩ := hrc.1 F.univ
  refine ⟨SFam.mk (pullback F.s (spMap j)) (pullback.snd F.s (spMap j)) ?_
    (isQProjOver_of_isPullback_spMap j sq F.qproj) u (hrc.2.1 F.univ u hu F.princ) ?_ ?_,
    pullback.fst F.s (spMap j), sq, hu⟩
  · exact (smoothOfRelativeDimension_isStableUnderBaseChange (n := h * (h + 1) / 2)).of_isPullback sq F.smooth
  · intro T t c hr hd hc
    have hd' : Dense {x : T | ((t ≫ spMap j) x).asIdeal = ⊥} := by
      refine hd.mono fun x hx => ?_
      have hx' : (t x).asIdeal = ⊥ := hx
      change Ideal.comap j (t x).asIdeal = ⊥
      exact (congrArg (Ideal.comap j) hx').trans (Ideal.comap_bot_of_injective j hi)
    obtain ⟨f₀, hf₀, hpb⟩ := F.rep T (t ≫ spMap j) (down j hj c) hr hd' hc
    refine ⟨pullback.lift f₀ t hf₀, pullback.lift_snd _ _ _, ?_⟩
    have hpb' : SiegPB c F.univ (pullback.lift f₀ t hf₀ ≫ pullback.fst F.s (spMap j)) := by
      rw [pullback.lift_fst]
      exact hpb
    exact pb_cancel hu hpb'
  · intro R _ _ x y t c hxy hx hy
    refine pullback.hom_ext ?_ hxy
    have e : (x ≫ pullback.fst F.s (spMap j)) ≫ F.s = (y ≫ pullback.fst F.s (spMap j)) ≫ F.s := by
      simp only [Category.assoc, pullback.condition, reassoc_of% hxy]
    exact F.inj R _ _ (t ≫ spMap j) (down j hj c) e (pb_comp hu hx) (pb_comp hu hy)

theorem siegRep {p M : ℕ} (F : SFam h M (zetaZP p M))
    (sm : SmoothOfRelativeDimension (h * (h + 1) / 2) F.s) (qc : QuasiCompact F.s) (pr : F.univ.Principal) (pts unr) :
    GlobalTheory.Models.SiegRep (⟨F.X, F.s, sm, qc, F.univ, pr, pts, unr⟩ : SiegelFamily h p M) := by
  unfold GlobalTheory.Models.SiegRep
  refine ⟨F.qproj, fun T t c hr _ hfl hc => ?_⟩
  exact F.existsUnique c hr (dense_generic_of_flat t) hc

end SFam

theorem SFam.exists_sRep_siegRep {p M : ℕ} (hM : M ≠ 0) (F : SFam h M (zetaZP p M)) (Ag : SiegelFamily h p M)
    (H : SRep Ag) : ∃ Ag' : SiegelFamily h p M, SRep Ag' ∧ GlobalTheory.Models.SiegRep Ag' := by
  obtain ⟨hsep, hrep⟩ := H
  obtain ⟨hr, hd⟩ := F.isReduced_and_dense
  have := Ag.smooth
  have : Smooth Ag.s := SmoothOfRelativeDimension.smooth (n := h * (h + 1) / 2) (f := Ag.s)
  have : IsReduced Ag.X := isReduced_of_smooth_of_isReduced Ag.s
  obtain ⟨f, hf, hpf⟩ := hrep F.X F.s F.univ hr hd F.princ
  obtain ⟨g, hg, hpg⟩ := F.rep Ag.X Ag.s Ag.univ inferInstance (dense_generic_of_flat Ag.s) Ag.princ
  have hfg : f ≫ g = 𝟙 _ :=
    F.hom_ext F.univ _ _ (by rw [Category.assoc, hg, hf, Category.id_comp]) (pb_comp hpg hpf) (pb_id _)
  have : IsSeparated (g ≫ F.s) := by rw [hg]; exact hsep
  have : IsSeparated g := IsSeparated.of_comp g F.s
  have : IsClosedImmersion (f ≫ g) := by rw [hfg]; infer_instance
  have : IsClosedImmersion f := IsClosedImmersion.of_comp f g
  have := Ag.qc
  have qc : QuasiCompact F.s := by rw [← hf]; infer_instance
  refine ⟨⟨F.X, F.s, F.smooth, qc, F.univ, F.princ, ?_, ?_⟩, ?_, ?_⟩
  · intro C O _ _ _ _ _ _ _ _ hu hp β o ho ha
    obtain ⟨y, hy, hpy⟩ := Ag.points C O hu hp β o ho ha
    exact ⟨y ≫ g, by rw [Category.assoc, hg, hy], pb_comp hpg hpy⟩
  · intro K _ x o h₁ h₂
    have key : ∀ (s₁ : Sp (DualNumber K) ⟶ Sp (ZP p M)) (o₁ : SiegPre h M (zetaZP p M) s₁),
        s₁ = (x ≫ f) ≫ Ag.s → SiegPB o₁ Ag.univ (x ≫ f) → SiegPB o₁ Ag.univ (constPt (x ≫ f)) →
        x ≫ f = constPt (x ≫ f) := by
      rintro s₁ o₁ rfl
      exact Ag.unram K (x ≫ f) o₁
    have hc : constPt (x ≫ f) = constPt x ≫ f := by simp only [constPt, Category.assoc]
    have e : x ≫ f = constPt x ≫ f := by
      rw [← hc]
      refine key _ o (by rw [Category.assoc, hf]) (pb_comp hpf h₁) ?_
      rw [hc]
      exact pb_comp hpf h₂
    calc x = x ≫ (f ≫ g) := by rw [hfg, Category.comp_id]
      _ = (x ≫ f) ≫ g := (Category.assoc _ _ _).symm
      _ = (constPt x ≫ f) ≫ g := by rw [e]
      _ = constPt x := by rw [Category.assoc, hfg, Category.comp_id]
  · exact F.sRep F.smooth qc F.princ _ _
  · exact F.siegRep F.smooth qc F.princ _ _

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem PELRep.exists_point {D : Datum H} {a : J → 𝓞 E} {bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La} {ρ : o}
    {t : TObj g k J b s} (R : PELRep D a bas ρ t) {K : Type} [Field K] (β : o →+* K) (hβ : Function.Injective β)
    (t' : TObj g k J b (spMap β)) (τ' : SAB H (Sp K)) (h' : IsPEL D a bas ρ t' τ') :
    ∃ x : Sp K ⟶ S, x ≫ s = spMap β ∧ TMap t' t x := by
  have hC : Function.Injective ((PowerSeries.C (R := K)).comp β) := PowerSeries.C_injective.comp hβ
  have e₁ : spMap (PowerSeries.C (R := K)) ≫ spMap β = spMap ((PowerSeries.C (R := K)).comp β) :=
    (spMap_comp' β PowerSeries.C).symm
  obtain ⟨t'', ht''⟩ := tObj_pull o g k J b (Sp K) (Sp (PowerSeries K)) (spMap β)
    (spMap ((PowerSeries.C (R := K)).comp β)) (spMap PowerSeries.C) t' e₁
  obtain ⟨τ'', hτ''⟩ := exists_isPEL_of_tmap E H D g J a bas k o b ρ (Sp K) (Sp (PowerSeries K)) (spMap β)
    (spMap ((PowerSeries.C (R := K)).comp β)) t' t'' τ' (spMap PowerSeries.C) e₁ ht'' h'
  obtain ⟨f, hf, hft⟩ := R.rep (PowerSeries K) ((PowerSeries.C (R := K)).comp β) t'' τ'' hC hτ''
  have e₂ : spMap (PowerSeries.constantCoeff (R := K)) ≫ spMap (PowerSeries.C (R := K)) = 𝟙 (Sp K) := by
    have : (PowerSeries.constantCoeff (R := K)).comp PowerSeries.C = RingHom.id K :=
      RingHom.ext fun x => PowerSeries.constantCoeff_C x
    rw [← spMap_comp', this]
    simp
  refine ⟨spMap PowerSeries.constantCoeff ≫ f, ?_, ?_⟩
  · rw [Category.assoc, hf, ← e₁, ← Category.assoc, e₂, Category.id_comp]
  · have hback : TMap t' t'' (spMap PowerSeries.constantCoeff) := by
      refine TMap.cancel ht'' ?_
      rw [e₂]
      exact TMap.refl t'
    exact TMap.comp hback hft

theorem exists_hom_of_basis {G : Type} [CommGroup G] {n : ℕ} (p : Fin n → G) :
    ∃ q : (Fin n → ℤ) → G, (∀ x y, q (x + y) = q x * q y) ∧ ∀ i, q (Pi.single i 1) = p i := by
  refine ⟨fun x => ∏ i, p i ^ x i, fun x y => ?_, fun i => ?_⟩
  · simp only [Pi.add_apply, zpow_add, Finset.prod_mul_distrib]
  · show ∏ j, p j ^ (Pi.single i (1 : ℤ) : Fin n → ℤ) j = p i
    rw [Finset.prod_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zpow_zero])
      (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same, zpow_one]

end GlobalTheory.ZM
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsRetractTensorTriple
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

noncomputable section

namespace GlobalTheory.Models

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

section Amp

variable {D : Datum H} {Xo : ∀ l : Level H, Moduli D l}

def Top.Amp {n N : ℕ} (T : Top Xo n N) : Prop :=
  ∃ k : ℕ, Nonempty (GlobalTheory.LN.AmpFrames T.t.G T.t.PP.L ((n ^ k) ^ 2))

def System.Amp (S : System Xo) : Prop := ∀ i, (S.T i).Amp

theorem topExists_iff_amp : TopExists ↔
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), 1 ≤ D.p + D.q →
      ∀ (Xo : ∀ l : Level H, Moduli D l) (n : ℕ), AuxiliaryInertOddPrime H n → ∃ J : ℕ, 1 ≤ J ∧ ∃ T : Top Xo n (n ^ J), T.Amp :=
  Iff.rfl

end Amp

section Refl

variable {U : Scheme.{0}} {F O : Type} [Field F] [CommRing O] {c : U ⟶ Sp F} {t₀ : SAB H U} {β : O →+* F}

def Cpt.Above.refl (C : Cpt c t₀ β) : C.Above C (RingHom.id O) (𝟙 U) (ObjComp.sabMapId t₀) where
  π := 𝟙 _
  π_over := by rw [show spMap (RingHom.id O) = 𝟙 _ from Spec.map_id _, Category.id_comp, Category.comp_id]
  fin := by
    have : IsIso (spMap (RingHom.id O)) := (show spMap (RingHom.id O) = 𝟙 _ from Spec.map_id _) ▸ inferInstance
    refine (fun w => ?_ : ∀ w : 𝟙 C.X ≫ C.s = C.s ≫ spMap (RingHom.id O), IsFinite (pullback.lift (𝟙 C.X) C.s w)) _
    have h : pullback.lift (𝟙 C.X) C.s w ≫ pullback.fst _ _ = 𝟙 _ := pullback.lift_fst _ _ _
    have : IsIso (pullback.lift (𝟙 C.X) C.s w) := IsIso.of_isIso_fac_right h
    infer_instance
  mu := ObjComp.sabMapId C.t
  j_comm := (Category.comp_id _).trans (Category.id_comp _).symm
  φ_comm := (Category.comp_id _).trans (Category.id_comp _).symm

end Refl

section Abelian

variable {O F : Type} [CommRing O] [Field F] (β : O →+* F) {X : Scheme.{0}} (s : X ⟶ Sp O) (t : SAB H X)

def Cpt.ofAbelian (hn : Geo.Tor.IsNormalScheme X) (hp : IsProjOver s) (hf : Flat s) (ha : IsProper t.G.hom)
    (t₀ : SAB H (pullback s (spMap β))) (m : SABMap t₀ t (𝟙 _ ≫ pullback.fst _ _)) :
    Cpt (pullback.snd s (spMap β)) t₀ β :=
  ⟨X, s, hn, hp, hf, 𝟙 _, Category.id_comp _, inferInstance, by simp, t, m, by simp [Point.abLocus_eq_univ]⟩

def tensorTriple (H : Host E) (A : Over X) [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A) : SAB H X where
  G := Serre.tensorObj (𝓞 E) (Serre.intAct A)
  semi := isSemiAbelian_of_isAbelianScheme _ ((Serre.isTensor (𝓞 E) (Serre.intAct A)).isAbelianScheme hA)
  act := (Serre.isTensor (𝓞 E) (Serre.intAct A)).algAct (𝓞 E)
  PP := (UU.CP.triv _).L
  cub := (UU.CP.triv _).c
  sym := isSymmetric_of_symmetry_generator _ _ (UU.CP.triv _).sym_gen (UU.CP.triv _).sym_rig
  adj := fun _ => ⟨⟨fun _ => 1⟩, ZJ.isGen_one_of_g_eq_one _
    (ZJ.div_g_eq_one _ _ (Out.Inh.linComb_triv_g _ _) (Out.Inh.linComb_triv_g _ _))⟩
  prim := ⟨⟨fun _ => 1⟩, ZJ.isGen_one_of_g_eq_one _
    (ZJ.div_g_eq_one _ _ (Out.Inh.linComb_triv_g _ _) fun _ _ => rfl)⟩

variable (A : Over X) [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A)

theorem isProper_tensorTriple : IsProper (tensorTriple H A hA).G.hom :=
  ((Serre.isTensor (𝓞 E) (Serre.intAct A)).isAbelianScheme hA).proper

theorem exists_retract_tensorTriple :
    ∃ (i : A ⟶ (tensorTriple H A hA).G) (r : (tensorTriple H A hA).G ⟶ A), i ≫ r = 𝟙 A := by
  let b := Module.Free.chooseBasis ℤ (𝓞 E)
  obtain ⟨j⟩ := b.index_nonempty
  exact ⟨_, _, (Serre.isTensor (𝓞 E) (Serre.intAct A)).tmul_mapLeft_self (b.coord j) (m := b j) (by simp)⟩

end Abelian

theorem flat_projSpace (R : Type) [CommRing R] (N : ℕ) : Flat (PSpace.str R N) :=
  haveI : IsZariskiLocalAtSource @Flat.{0} := HasRingHomProperty.instIsZariskiLocalAtSource
  IsZariskiLocalAtSource.of_openCover (P := @Flat) (ProjSpace.chartCover R N) fun (i : Fin (N + 1)) => by
    change Flat (ProjSpace.chartι R N i ≫ _)
    rw [ProjSpace.chartι_str, HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 (inferInstanceAs (Module.Flat R (MvPolynomial _ R)))

theorem isNormalScheme_projSpace (R : Type) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] (N : ℕ) :
    Geo.Tor.IsNormalScheme (PSpace R N) := by
  refine (isNormalScheme_iff_pred _).1 (IsNormalScheme.of_forall_exists_isOpenImmersion fun x => ?_)
  obtain ⟨i, y, hy⟩ := (ProjSpace.chartCover R N).exists_eq x
  exact ⟨_, ProjSpace.chartι R N i, ProjSpace.isOpenImmersion_chartι R N i, IsNormalScheme.of_pred (ZJ.isNormalScheme_sp _), y, hy⟩

end GlobalTheory.Models

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.ModuliSpaces.NotPelRepOfTwoPoints
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
namespace GlobalTheory.ZM

variable {o : Type} [CommRing o] {S : Scheme.{0}} {g k : ℕ} {J : Type} {b : TBase o k} {s : S ⟶ Sp o}
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

namespace DimZero
open Out.Inh GlobalTheory.ZM.Model

theorem translT_zero {T : Over S} (x : T ⟶ (zeroPolAV S).A) : (Out.translT (zeroPolAV S).A x).left = 𝟙 _ := by
  have : Out.translT (zeroPolAV S).A x = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext
    · simp [Out.translT]
    · exact toUnit_unique _ _
  rw [this]; rfl

theorem exists_gen {X : Scheme.{0}} (L : LB X) (hL : ∀ i j, L.g i j = 1) : ∃ t : L.Gen, t.IsGen ∧ ∀ i, t.s i = 1 :=
  ⟨⟨fun _ => 1⟩, fun i j => by
    rw [hL, _root_.one_mul]; exact (map_one _).trans (map_one _).symm, fun _ => rfl⟩

theorem corr_comm {X Y : Scheme.{0}} (L : LB X) [Unique L.ι] {K : Type} [Fintype K] (φ φ' : K → (Y ⟶ X)) (ε : K → ℤ)
    (a : LB.Gen (LB.LinComb L φ ε)) (b : LB.Gen (LB.LinComb L φ' ε)) (h h' : Y ⟶ Y) (hh : h = 𝟙 Y) (hh' : h' = 𝟙 Y)
    (c : LB.Gen (LB.LinComb L (Y := Y) (K := PEmpty) PEmpty.elim PEmpty.elim)) (hc : ∀ j, c.s j = 1) :
    LB.Gen.Corr L _ _ _ _ (LB.mulGen _ _ _ _ _ a (LB.pullGen _ _ _ b h))
      (LB.mulGen _ _ _ _ _ (LB.mulGen _ _ _ _ _ b (LB.pullGen _ _ _ a h')) c) := by
  subst hh hh'
  intro j j' _ _ _
  obtain rfl : j = fun _ => default := Subsingleton.elim _ _
  obtain rfl : j' = fun _ => default := Subsingleton.elim _ _
  have e1 : ∀ (V W : Y.Opens) (h1 : V ≤ W) (U U' : Y.Opens) (h2 : W ≤ U) (h3 : W ≤ U') (u : Γ(Y, U)ˣ) (v : Γ(Y, U')ˣ),
      res h1 (res h2 u * res h3 v) = res (h1.trans h2) u * res (h1.trans h3) v := by
    intros; rw [map_mul, DVR.res_res', DVR.res_res']
  refine (e1 _ _ _ _ _ _ _ _ _).trans (Eq.trans ?_ (e1 _ _ _ _ _ _ _ _ _).symm)
  refine Eq.trans ?_ (congrArg₂ (· * ·) (e1 _ _ _ _ _ _ _ _ _) ((congrArg _ (hc _)).trans (map_one _))).symm
  rw [_root_.mul_one, _root_.mul_comm]
  refine congrArg₂ (· * ·) ?_ ?_
  · exact (DVR.res_res' _ _ _)
  · exact (DVR.res_res' _ _ _).symm

theorem weilIs_zero (L : LB (zeroPolAV S).A.left) [Unique L.ι] (hL : ∀ i j, L.g i j = 1) (n : ℤ) {T : Over S}
    (x y : T ⟶ (zeroPolAV S).A) : Out.WeilIs (zeroPolAV S).A L n x y 1 := by
  intro p
  have ex : ∀ z : Out.overRes (T := T) ⊤ ⟶ (zeroPolAV S).A, ∃ θ : Out.ThetaGrp _ L n _, θ.pt = z := fun z => by
    obtain ⟨t, ht, -⟩ := exists_gen (Out.thetaLB _ L n z) (linComb_g_one L hL _ _)
    exact ⟨⟨z, t, ht⟩, rfl⟩
  refine ⟨⊤, trivial, ?_, fun θx θy _ _ => ?_⟩
  · obtain ⟨θx, hx⟩ := ex (Out.overResι ⊤ ≫ x)
    obtain ⟨θy, hy⟩ := ex (Out.overResι ⊤ ≫ y)
    exact ⟨θx, θy, hx, hy⟩
  · have hc : Out.unitRes (T := T) ⊤ 1 = 1 := map_one _
    rw [hc]
    exact corr_comm L _ _ _ _ _ _ _ (translT_zero _) (translT_zero _) _
      (fun j => (congrArg _ (map_one _)).trans (map_one _))

def zeroSieg (k : ℕ) {B : Type} [CommRing B] (ζ : B) (s : S ⟶ Sp B) : SiegPre 0 k ζ s where
  A := (zeroPolAV S).A
  comm := (zeroPolAV S).isAb.comm
  ab := (zeroPolAV S).isAb
  P := trivLB _
  isLB := trivLB_isLB _
  rig₁ := (exists_gen _ (linComb_triv_g _ _)).imp fun _ h => h.1
  rig₂ := (exists_gen _ (linComb_triv_g _ _)).imp fun _ h => h.1
  symm := lbIso_of_g _ _ (fun _ _ => rfl) (linComb_triv_g _ _)
  lev := fun _ => 1
  lev_add := fun _ _ => toUnit_unique _ _
  lev_tors := fun _ => toUnit_unique _ _
  geom := fun K _ _ x β z _ _ => by
    refine ⟨fun a => ⟨fun _ => ⟨0, Subsingleton.elim _ _⟩, fun _ => toUnit_unique _ _⟩,
      fun _ _ => ⟨0, toUnit_unique _ _⟩, fun a a' => ?_⟩
    have h1 : unitOn (z ^ (2 * omegaStd a a')) = 1 := by
      have : omegaStd a a' = 0 := by simp [omegaStd]
      rw [this, mul_zero, zpow_zero]
      exact map_one _
    rw [h1]
    exact @weilIs_zero S _ (inferInstanceAs (Unique (PUnit → PUnit))) (linComb_triv_g _ _) _ _ _ _

theorem principal_zeroSieg (k : ℕ) {B : Type} [CommRing B] (ζ : B) (s : S ⟶ Sp B) : (zeroSieg k ζ s).Principal := by
  refine ⟨?_, fun _ _ _ => toUnit_unique _ _⟩
  generalize hM : (zeroSieg k ζ s).diag = M
  have hg : ∀ i j, M.g i j = 1 := by subst hM; exact linComb_triv_g _ _
  have hU : ∃ i, M.U i = ⊤ := by
    subst hM; exact ⟨fun _ => PUnit.unit, top_unique fun y _ => Set.mem_iInter.2 fun _ => trivial⟩
  obtain ⟨i₀, hi₀⟩ := hU
  change LB (𝟙_ (Over S)).left at M
  change Out.RelAmple (𝟙_ (Over S)) M
  intro U hU
  haveI : IsIso (𝟙_ (Over S)).hom := by show IsIso (𝟙 S); infer_instance
  let Y := ((𝟙_ (Over S)).hom ⁻¹ᵁ U).toScheme
  have hp : ∀ i j, (Out.powOver (𝟙_ (Over S)) M U 1).g i j = 1 := fun i j => by
    exact linComb_g_one M hg _ _ i j
  let s0 : LB.Sec (Out.powOver (𝟙_ (Over S)) M U 1) :=
    ⟨fun _ => 1, by
      intro i j; rw [hp, Units.val_one, _root_.one_mul]; repeat erw [map_one]
      all_goals rfl⟩
  have hD : Out.nonzeroLocus s0 = ⊤ := by
    apply top_unique
    intro x _
    simp only [Out.nonzeroLocus, s0, Scheme.basicOpen_one]
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i₀, Set.mem_iInter.2 fun _ => by
      show _ ∈ M.U i₀
      rw [hi₀]; trivial⟩
  refine ⟨1, le_rfl, 0, fun _ => s0, by simp only [iSup_const]; exact hD,
    fun _ => ⟨?_, fun _ => 1, ?_, ?_⟩⟩
  · rw [hD]
    have : IsAffine Y := hU
    exact isAffineOpen_top Y
  · intro j k
    erw [map_one]; (try erw [map_one]); (try erw [map_one]); exact (_root_.mul_one _).symm
  · intro p
    obtain ⟨a, rfl⟩ := surj_appLE ((𝟙_ (Over S)).hom ∣_ U) _ hD le_top p
    exact ⟨MvPolynomial.C a, MvPolynomial.eval₂Hom_C _ _ _⟩

def zeroBas (H : Host E) : (Fin (2 * 0) → ℤ) ≃ₗ[ℤ] (Test.zeroDatum H).La :=
  haveI : Subsingleton (Fin (2 * 0) → ℤ) := ⟨fun _ _ => funext fun i => i.elim0⟩
  haveI : Subsingleton (Test.zeroDatum H).La := inferInstanceAs (Subsingleton PUnit)
  LinearEquiv.ofSubsingleton _ _

theorem pelRep_zero [_root_.IsReduced o] (D : Datum H) (a : J → 𝓞 E) (bas : (Fin (2 * 0) → ℤ) ≃ₗ[ℤ] D.La) (ρ : o)
    (b : TBase o k) : PELRep D a bas ρ (zeroObj J b (𝟙 (Sp o))) where
  qproj := OnePoint.isQProjOver_id o
  flat := inferInstance
  red := inferInstance
  rep := fun _ _ _ _ β t' _ _ _ => ⟨spMap β, Category.comp_id _, tmap_zero _ t' _⟩
  inj := fun _ _ _ _ _ _ _ h _ _ => by simpa using h

end DimZero

end GlobalTheory.ZM
end
end

