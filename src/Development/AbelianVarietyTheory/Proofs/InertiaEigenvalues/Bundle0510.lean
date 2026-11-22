import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0477
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0478
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0476
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0475
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0479
import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LeAdjoinCompatibleRootsOfFiniteKummerTowerStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.le_adjoin_compatibleRoots_of_finite_kummerTower : ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) (ϖ : PiSys l e) (F : IntermediateField ℚ_[l] (Om l)), FiniteDimensional ℚ_[l] F → F ≤ ϖ.Kinf → ∃ n : ℕ, F ≤ IntermediateField.adjoin ℚ_[l] {ϖ.seq n ^ e} := by
  first | exact @GlobalTheory.KinfFin.main | exact GlobalTheory.KinfFin.main | (intros; apply GlobalTheory.KinfFin.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LenModMonoLeft
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace GlobalTheory

theorem lenMod_mono_left : ∀ {O M : Type} [CommRing O] [AddCommGroup M] [Module O M]
    (S S' H : Submodule O M), S ≤ S' → BlochKatoDuality.lenMod S H ≤ BlochKatoDuality.lenMod S' H := by
  intro O M _ _ _ S S' H hS

  have hle : S ⊔ H ≤ S' ⊔ H := sup_le_sup_right hS H
  let f := Submodule.mapQ (H.comap (S ⊔ H).subtype) (H.comap (S' ⊔ H).subtype)
    (Submodule.inclusion hle) (fun x hx => by simpa using hx)
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
    rw [Submodule.Quotient.mk_eq_zero]
    simpa using hx
  exact Module.length_le_of_injective f hf

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthModuloSpanLeOfForallFinset
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual

namespace GlobalTheory.Pass.LocDual

theorem lenMod_eq_height_map {O M : Type} [CommRing O] [AddCommGroup M] [Module O M]
    (S H : Submodule O M) : BlochKatoDuality.lenMod S H = Order.height (S.map H.mkQ) := by
  show Module.length O (↥(S ⊔ H) ⧸ H.comap (S ⊔ H).subtype) = _
  have hker : LinearMap.ker (H.mkQ ∘ₗ (S ⊔ H).subtype) = H.comap (S ⊔ H).subtype := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  have hrange : LinearMap.range (H.mkQ ∘ₗ (S ⊔ H).subtype) = S.map H.mkQ := by
    rw [LinearMap.range_comp, Submodule.range_subtype, Submodule.map_sup, Submodule.mkQ_map_self,
      sup_bot_eq]
  rw [← Module.length_submodule]
  exact ((Submodule.quotEquivOfEq _ _ hker.symm).trans
    ((H.mkQ ∘ₗ (S ⊔ H).subtype).quotKerEquivRange.trans (LinearEquiv.ofEq _ _ hrange))).length_eq

theorem height_map_span_le_of_finset {O M N : Type} [CommRing O] [AddCommGroup M] [Module O M]
    [AddCommGroup N] [Module O N] (f : M →ₗ[O] N) (S : Set M) (b : ℕ∞)
    (h : ∀ F : Finset M, (↑F : Set M) ⊆ S →
      Order.height ((Submodule.span O (↑F : Set M)).map f) ≤ b) :
    Order.height ((Submodule.span O S).map f) ≤ b := by
  classical
  rw [Order.height_le_iff]
  intro p hp

  have hx : ∀ i : Fin p.length, ∃ x ∈ p i.succ, x ∉ p i.castSucc :=
    fun i => SetLike.exists_of_lt (p.step i)
  choose x hxin hxout using hx

  have hfin : ∀ i : Fin p.length, ∃ F : Finset M, (↑F : Set M) ⊆ S ∧
      x i ∈ (Submodule.span O (↑F : Set M)).map f := by
    intro i
    have hxi : x i ∈ (Submodule.span O S).map f := hp (p.monotone (Fin.le_last i.succ) (hxin i))
    obtain ⟨y, hyS, hyx⟩ := Submodule.mem_map.mp hxi
    obtain ⟨T, hTS, hyT⟩ := Submodule.mem_span_finite_of_mem_span hyS
    exact ⟨T, hTS, Submodule.mem_map.mpr ⟨y, hyT, hyx⟩⟩
  choose F hFS hxF using hfin
  let G : Finset M := Finset.univ.biUnion F
  have hGS : (↑G : Set M) ⊆ S := by
    intro z hz
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp hz
    exact hFS i hi
  have hFG : ∀ i, Submodule.span O (↑(F i) : Set M) ≤ Submodule.span O (↑G : Set M) := fun i =>
    Submodule.span_mono (fun z hz => Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hz⟩)

  let Q := (Submodule.span O (↑G : Set M)).map f
  let q : LTSeries (Submodule O N) := LTSeries.mk p.length (fun j => p j ⊓ Q) (by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    dsimp only
    refine lt_of_le_of_ne (inf_le_inf_right _ (p.monotone (Fin.castSucc_le_succ i))) ?_
    intro heq
    have h1 : x i ∈ p i.succ ⊓ Q :=
      Submodule.mem_inf.mpr ⟨hxin i, Submodule.map_mono (hFG i) (hxF i)⟩
    rw [← heq] at h1
    exact hxout i (Submodule.mem_inf.mp h1).1)
  calc (p.length : ℕ∞) = q.length := rfl
    _ ≤ Order.height Q := Order.length_le_height inf_le_right
    _ ≤ b := h G hGS

theorem lenMod_span_le_of_finset : ∀ {O M : Type} [CommRing O] [AddCommGroup M] [Module O M]
    (S : Set M) (H : Submodule O M) (b : ℕ∞),
    (∀ F : Finset M, (↑F : Set M) ⊆ S → BlochKatoDuality.lenMod (Submodule.span O (↑F : Set M)) H ≤ b) →
    BlochKatoDuality.lenMod (Submodule.span O S) H ≤ b := by
  intro O M _ _ _ S H b h
  rw [lenMod_eq_height_map]
  apply height_map_span_le_of_finset H.mkQ S b
  intro F hF
  rw [← lenMod_eq_height_map]
  exact h F hF

end GlobalTheory.Pass.LocDual
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftAllOfBlochKatoLiftingFamilyAtPlace
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.Pass.LocDirect

theorem isSubFam_of_fintype {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {ι : Type} {k : ℕ} (Ms : ι → (G →* Matrix (Fin k) (Fin k) LL)) (W : GRep G Qp LL O)
    {κ : Type} [Fintype κ] (x : κ → ι) (p : κ → W.V →ₗ[LL] (Fin k → LL))
    (h1 : ∀ j g v, p j (W.ρ g v) = (Ms (x j) g).mulVec (p j v)) (h2 : ∀ v, (∀ j, p j v = 0) → v = 0) :
    IsSubFam Ms W := by
  classical
  let e := Fintype.equivFin κ
  refine ⟨Fintype.card κ, fun m => x (e.symm m), fun m => p (e.symm m), fun m g v => h1 _ g v,
    fun v hv => h2 v fun j => ?_⟩
  simpa using hv (e j)

variable {D : D7} (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

theorem loc_eq_map {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (g : Br.G D.nbr i w hw) :
    Br.loc D.nbr i w hw M g =
      (mapM (toK D.nd i) M ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd)).map (Br.toLLK (D.nbr i w hw)) := by
  ext a b
  simp only [Br.loc, Br.locM, Br.locO, mapM, MonoidHom.coe_comp, Function.comp_apply, RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_coe, RingHom.mapMatrix_apply, Matrix.map_apply, toK]
  exact congrArg Subtype.val (Br.toLLK_alg (D.nbr i w hw) _).symm

end GlobalTheory.Pass.LocDirect

namespace GlobalTheory.Pass.LocDirect

variable {D : D7} (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

theorem exists_locEmb (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) {k : ℕ}
    (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (x₀ : D.nd.X i)
    (j : (Fin k → KK D.nd i) →ₗ[KK D.nd i] (Fin D.R.nV → KK D.nd i)) (hj : Function.Injective j)
    (hjM : ∀ g v, j ((mapM (toK D.nd i) M g).mulVec v) = (mapM (toK D.nd i) (rTwO D.nd i r x₀) g).mulVec (j v)) :
    ∃ J : Matrix (Fin D.R.nV) (Fin k) (Br.LL D.nbr i w hw),
      (∀ v, J.mulVec v = 0 → v = 0) ∧
      ∀ g, J * Br.loc D.nbr i w hw M g = Br.loc D.nbr i w hw (rTwO D.nd i r x₀) g * J := by
  classical
  obtain ⟨l, hl⟩ := LinearMap.exists_leftInverse_of_injective j (LinearMap.ker_eq_bot.mpr hj)
  have hLJ : LinearMap.toMatrix' l * LinearMap.toMatrix' j = 1 := by
    rw [← LinearMap.toMatrix'_comp, hl, LinearMap.toMatrix'_id]
  have hJM : ∀ γ, LinearMap.toMatrix' j * mapM (toK D.nd i) M γ =
      mapM (toK D.nd i) (rTwO D.nd i r x₀) γ * LinearMap.toMatrix' j := by
    intro γ
    have e : j ∘ₗ Matrix.toLin' (mapM (toK D.nd i) M γ) =
        Matrix.toLin' (mapM (toK D.nd i) (rTwO D.nd i r x₀) γ) ∘ₗ j := by
      refine LinearMap.ext fun v => ?_
      rw [LinearMap.comp_apply, LinearMap.comp_apply, Matrix.toLin'_apply, Matrix.toLin'_apply, hjM]
    have := congrArg LinearMap.toMatrix' e
    simpa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin'] using this
  set f := Br.toLLK (D.nbr i w hw)
  refine ⟨(LinearMap.toMatrix' j).map f, fun v hv => ?_, fun g => ?_⟩
  · have h1 : ((LinearMap.toMatrix' l).map f * (LinearMap.toMatrix' j).map f) = 1 := by
      rw [← Matrix.map_mul, hLJ, Matrix.map_one _ (map_zero f) (map_one f)]
    calc v = ((LinearMap.toMatrix' l).map f * (LinearMap.toMatrix' j).map f).mulVec v := by
          rw [h1, Matrix.one_mulVec]
      _ = 0 := by rw [← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
  · rw [loc_eq_map, loc_eq_map, ← Matrix.map_mul, ← Matrix.map_mul, hJM]

end GlobalTheory.Pass.LocDirect

namespace GlobalTheory.Pass.LocDirect

variable {D : D7} (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

theorem isSubFam_of_isSubSumOf (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (Xs : Set (D.nd.X i))
    {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (hSub : SubTw i r Xs M)
    (hM : Continuous fun g => M g) {a : ℕ} (x : Fin a → D.nd.X i) (hx : ∀ j, x j ∈ Xs)
    (hc : ∀ j, Continuous fun g => Br.loc D.nbr i w hw (rTwO D.nd i r (x j)) g)
    (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i))
    (hst : ∀ γ : GE D.nd, ∀ y ∈ Y,
      (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x j)) γ).mulVec (y j)) ∈ Y)
    (Wr : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw))
    (h : BlochKatoDuality.IsSubSumOf Wr.ρ (Xgrep i w hw r x hc Y hst).ρ (ModuleGaloisRepresentation i w hw M hM).ρ) :
    IsSubFam (fun x : ↥Xs => Br.loc D.nbr i w hw (rTwO D.nd i r x)) Wr := by
  classical
  obtain ⟨-, x₀, hx₀, j, hj, hjM⟩ := hSub
  obtain ⟨J, hJi, hJ⟩ := exists_locEmb i w hw r M x₀ j hj hjM
  obtain ⟨a', b', p, q, hp, hq, hinj⟩ := h
  let cX : Fin a → (↥(XV i w hw Y) →ₗ[Br.LL D.nbr i w hw] (Fin D.R.nV → Br.LL D.nbr i w hw)) :=
    fun m => LinearMap.proj m ∘ₗ (XV i w hw Y).subtype
  let P : (Fin a' × Fin a) ⊕ Fin b' → Wr.V →ₗ[Br.LL D.nbr i w hw] (Fin D.R.nV → Br.LL D.nbr i w hw) :=
    Sum.elim (fun ij => cX ij.2 ∘ₗ (p ij.1 : Wr.V →ₗ[Br.LL D.nbr i w hw] ↥(XV i w hw Y)))
      (fun m => Matrix.mulVecLin J ∘ₗ (q m : Wr.V →ₗ[Br.LL D.nbr i w hw] (Fin k → Br.LL D.nbr i w hw)))
  let xf : (Fin a' × Fin a) ⊕ Fin b' → ↥Xs := Sum.elim (fun ij => ⟨x ij.2, hx ij.2⟩) (fun _ => ⟨x₀, hx₀⟩)
  refine isSubFam_of_fintype _ Wr xf P ?_ ?_
  · rintro (⟨m, n⟩ | m) g v
    · have e1 := hp m g v
      change cX n (p m (Wr.ρ g v)) = (Br.loc D.nbr i w hw (rTwO D.nd i r (x n)) g).mulVec (cX n (p m v))
      rw [e1]
      rfl
    · have e1 := hq m g v
      change J.mulVec (q m (Wr.ρ g v)) = (Br.loc D.nbr i w hw (rTwO D.nd i r x₀) g).mulVec (J.mulVec (q m v))
      rw [e1]
      have key : ∀ u : Fin k → Br.LL D.nbr i w hw, J.mulVec ((Br.loc D.nbr i w hw M g).mulVec u) =
          (Br.loc D.nbr i w hw (rTwO D.nd i r x₀) g).mulVec (J.mulVec u) := fun u => by
        rw [Matrix.mulVec_mulVec, hJ, ← Matrix.mulVec_mulVec]
      exact key (q m v)
  · intro v hv
    refine hinj v (fun m => ?_) (fun m => hJi _ (hv (Sum.inr m)))
    apply Subtype.ext
    funext n
    exact hv (Sum.inl (m, n))

end GlobalTheory.Pass.LocDirect

namespace GlobalTheory.Pass.LocDirect

theorem liftAll_of_liftFamW : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))),
    GoodR D.nd i r → ∀ (Xs : Set (D.nd.X i)) (e : ℕ), LiftFamW i w hw (fun x : ↥Xs => rTwO D.nd i r x) e →
    ∀ {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)), SubTw i r Xs M →
    ∀ (hM : Continuous fun g => M g) (a : ℕ) (x : Fin a → D.nd.X i), (∀ j, x j ∈ Xs) →
    ∀ (hc : ∀ j, Continuous fun g => Br.loc D.nbr i w hw (rTwO D.nd i r (x j)) g)
      (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i))
      (hst : (∀ γ : GE D.nd, ∀ y ∈ Y,
        (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x j)) γ).mulVec (y j)) ∈ Y)),
    BlochKatoDuality.LiftAll (Br.PD D.loc D.nbr i w hw) (GlobalTheory.Pass.LocDirect.Xgrep i w hw r x hc Y hst)
      (GlobalTheory.Pass.LocDirect.ModuleGaloisRepresentation i w hw M hM) e := by
  intro D i w hw r _ Xs e hL k M hSub hM a x hx hc Y hst W₁ W₂ h₁ h₂ L₁ L₂ F hF
  exact hL W₁ W₂ (isSubFam_of_isSubSumOf i w hw r Xs M hSub hM x hx hc Y hst W₁ h₁)
    (isSubFam_of_isSubSumOf i w hw r Xs M hSub hM x hx hc Y hst W₂ h₂) L₁ L₂ F hF

end GlobalTheory.Pass.LocDirect
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftAllSubSumsOfLiftFamilyMatrixFamily
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual

noncomputable section

namespace GlobalTheory.Pass.LocDual

section Gen

variable {G : Type} [Group G] [TopologicalSpace G] {Qp : Type} [Field Qp]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]

theorem isSubFam_of_isSubSumOf {ι : Type} {k : ℕ} (Ms : ι → (G →* Matrix (Fin k) (Fin k) LL))
    (W A A' : GRep G Qp LL O) (hW : BlochKatoDuality.IsSubSumOf W.ρ A.ρ A'.ρ) (hA : IsSubFam Ms A)
    (hA' : IsSubFam Ms A') : IsSubFam Ms W := by
  obtain ⟨a, b, p, q, hp, hq, hinj⟩ := hW
  obtain ⟨a₁, x₁, p₁, hp₁, hinj₁⟩ := hA
  obtain ⟨a₂, x₂, p₂, hp₂, hinj₂⟩ := hA'
  let e : Fin (a * a₁ + b * a₂) ≃ (Fin a × Fin a₁) ⊕ (Fin b × Fin a₂) :=
    finSumFinEquiv.symm.trans (Equiv.sumCongr finProdFinEquiv.symm finProdFinEquiv.symm)
  let X : (Fin a × Fin a₁) ⊕ (Fin b × Fin a₂) → ι :=
    Sum.elim (fun ij => x₁ ij.2) (fun ij => x₂ ij.2)
  let P : (Fin a × Fin a₁) ⊕ (Fin b × Fin a₂) → W.V →ₗ[LL] (Fin k → LL) :=
    Sum.elim (fun ij => (p₁ ij.2).comp (p ij.1)) (fun ij => (p₂ ij.2).comp (q ij.1))
  refine ⟨a * a₁ + b * a₂, X ∘ e, P ∘ e, ?_, ?_⟩
  · intro j g v
    simp only [Function.comp]
    generalize e j = s
    rcases s with ⟨i, j'⟩ | ⟨i, j'⟩
    · simp only [P, X, Sum.elim_inl, LinearMap.comp_apply, hp, hp₁]
    · simp only [P, X, Sum.elim_inr, LinearMap.comp_apply, hq, hp₂]
  · intro v hv
    apply hinj v
    · intro i
      apply hinj₁
      intro j'
      have h := hv (e.symm (Sum.inl (i, j')))
      simpa [P] using h
    · intro i
      apply hinj₂
      intro j'
      have h := hv (e.symm (Sum.inr (i, j')))
      simpa [P] using h

end Gen

section OnePD

theorem liftAll_of_liftFam :
    ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {ι : Type} {k : ℕ} (Ms : ι → (G →* Matrix (Fin k) (Fin k) LL)) (e : ℕ)
    (A A' : GRep G Qp LL O), LiftFam (O := O) PD Ms e → IsSubFam Ms A → IsSubFam Ms A' → BlochKatoDuality.LiftAll PD A A' e := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL O _ _ _ _ _ ι k Ms e A A' hL hA hA'
  intro W₁ W₂ h₁ h₂ L₁ L₂ F hF
  exact hL W₁ W₂ (isSubFam_of_isSubSumOf Ms W₁ A A' h₁ hA hA')
    (isSubFam_of_isSubSumOf Ms W₂ A A' h₂ hA hA') L₁ L₂ F hF

end OnePD

end GlobalTheory.Pass.LocDual

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftableDescendsFromLargerCoefficientField
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BaseCoef

noncomputable section

namespace GlobalTheory.CoefDescent

section General
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {E E' : Type} [Field E] [Algebra Qp E] [Field E'] [Algebra Qp E']
    {O O' : Type} [CommRing O] [Algebra O E] [CommRing O'] [Algebra O' E']

theorem blochKatoCocycle_comp_equivariant_map
    {V : Type} [AddCommGroup V] [Module E V] [Module Qp V] [IsScalarTower Qp E V]
    [Module O V] [IsScalarTower O E V] {ρ : Representation E G V}
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul E V]
    {V' : Type} [AddCommGroup V'] [Module E' V'] [Module Qp V'] [IsScalarTower Qp E' V']
    [Module O' V'] [IsScalarTower O' E' V'] {ρ' : Representation E' G V'}
    [TopologicalSpace V'] [ContinuousAdd V'] [ContinuousConstSMul E' V']
    (L : Lattice (O := O) ρ) (L' : Lattice (O := O') ρ') (φ : V →ₗ[Qp] V')
    (he : ∀ g x, φ (ρ g x) = ρ' g (φ x)) (hc : Continuous φ) (hT : ∀ x ∈ L.T, φ x ∈ L'.T)
    (c : G → V) (h : c ∈ latticeFiniteCocycles PD L) : (fun g => φ (c g)) ∈ latticeFiniteCocycles PD L' := by
  obtain ⟨⟨⟨hc1, hc2⟩, hc3⟩, -, x, hx⟩ := h
  have hz : (fun g => φ (c g)) ∈ continuousCocycles ρ' := by
    refine ⟨hc.comp hc1, fun g h => ?_⟩
    change φ (c (g * h)) = φ (c g) + ρ' g (φ (c h))
    rw [hc2, map_add, he]
  refine ⟨⟨hz, fun g _ => hT _ (hc3 g (Set.mem_univ g))⟩, hz, LinearMap.rTensor B φ x, fun g => ?_⟩
  have key : ∀ y : V ⊗[Qp] B, LinearMap.rTensor B φ (actVB PD ρ g y) =
      actVB PD ρ' g (LinearMap.rTensor B φ y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [actVB, he]
    | add a b ha hb => simp only [map_add, ha, hb]
  rw [← key, ← map_sub, ← hx, LinearMap.rTensor_tmul]

theorem liftF_of_retract
    {V₁ : Type} [AddCommGroup V₁] [Module E V₁] [Module Qp V₁] [IsScalarTower Qp E V₁]
    [Module O V₁] [IsScalarTower O E V₁] {ρ₁ : Representation E G V₁}
    [TopologicalSpace V₁] [ContinuousAdd V₁] [ContinuousConstSMul E V₁]
    {V₂ : Type} [AddCommGroup V₂] [Module E V₂] [Module Qp V₂] [IsScalarTower Qp E V₂]
    [Module O V₂] [IsScalarTower O E V₂] {ρ₂ : Representation E G V₂}
    [TopologicalSpace V₂] [ContinuousAdd V₂] [ContinuousConstSMul E V₂]
    {W₁ : Type} [AddCommGroup W₁] [Module E' W₁] [Module Qp W₁] [IsScalarTower Qp E' W₁]
    [Module O' W₁] [IsScalarTower O' E' W₁] {σ₁ : Representation E' G W₁}
    [TopologicalSpace W₁] [ContinuousAdd W₁] [ContinuousConstSMul E' W₁]
    {W₂ : Type} [AddCommGroup W₂] [Module E' W₂] [Module Qp W₂] [IsScalarTower Qp E' W₂]
    [Module O' W₂] [IsScalarTower O' E' W₂] {σ₂ : Representation E' G W₂}
    [TopologicalSpace W₂] [ContinuousAdd W₂] [ContinuousConstSMul E' W₂]
    {L₁ : Lattice (O := O) ρ₁} {L₂ : Lattice (O := O) ρ₂}
    {M₁ : Lattice (O := O') σ₁} {M₂ : Lattice (O := O') σ₂}
    (F : LatHom L₁ L₂) (F' : LatHom M₁ M₂)
    (ι : V₂ →ₗ[Qp] W₂) (R₁ : W₁ →ₗ[Qp] V₁) (R₂ : W₂ →ₗ[Qp] V₂)
    (ιe : ∀ g x, ι (ρ₂ g x) = σ₂ g (ι x)) (ιc : Continuous ι) (ιT : ∀ x ∈ L₂.T, ι x ∈ M₂.T)
    (R₁e : ∀ g x, R₁ (σ₁ g x) = ρ₁ g (R₁ x)) (R₁c : Continuous R₁) (R₁T : ∀ x ∈ M₁.T, R₁ x ∈ L₁.T)
    (R₂e : ∀ g x, R₂ (σ₂ g x) = ρ₂ g (R₂ x)) (R₂T : ∀ x ∈ M₂.T, R₂ x ∈ L₂.T)
    (hret : ∀ x, R₂ (ι x) = x) (hF : ∀ x, R₂ (F'.f x) = F.f (R₁ x))
    (e : ℕ) (h : F'.LiftF PD e) : F.LiftF PD e := by
  intro c hc
  have h1 := h _ (blochKatoCocycle_comp_equivariant_map PD L₂ M₂ ι ιe ιc ιT c hc)
  obtain ⟨_, ⟨d, hd, rfl⟩, _, ⟨y, hy, rfl⟩, hsum⟩ := Submodule.mem_sup.1 h1
  refine Submodule.mem_sup.2 ⟨_, ⟨_, blochKatoCocycle_comp_equivariant_map PD M₁ L₁ R₁ R₁e R₁c R₁T d hd, rfl⟩, _,
    ⟨R₂ y, R₂T y hy, rfl⟩, ?_⟩
  funext g
  have h2 := congrArg R₂ (congrFun hsum g)
  change R₂ (F'.f (d g) + (σ₂ g y - y)) = R₂ (((PD.p : O') ^ e) • ι (c g)) at h2
  change F.f (R₁ (d g)) + (ρ₂ g (R₂ y) - R₂ y) = ((PD.p : O) ^ e) • c g
  rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul, map_nsmul, hret, map_add, map_sub, hF, R₂e] at h2
  rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul, h2]

end General

section Maps
variable {Qp E E' : Type} [Field Qp] [Field E] [Algebra Qp E] [Field E'] [Algebra Qp E']
  {V : Type} [AddCommGroup V] [Module E V] [Module Qp V] [IsScalarTower Qp E V]
  {V' : Type} [AddCommGroup V'] [Module E V'] [Module Qp V'] [IsScalarTower Qp E V']
  {k k' : ℕ}

def emb (j : E →ₐ[Qp] E') (b : Module.Basis (Fin k) E V) : V →ₗ[Qp] (Fin k → E') :=
  LinearMap.pi fun i => j.toLinearMap ∘ₗ (b.coord i).restrictScalars Qp

theorem emb_apply (j : E →ₐ[Qp] E') (b : Module.Basis (Fin k) E V) (v : V) (i : Fin k) :
    emb j b v i = j (b.repr v i) := rfl

def ret (r : E' →ₗ[Qp] E) (b : Module.Basis (Fin k) E V) : (Fin k → E') →ₗ[Qp] V :=
  (b.equivFun.symm.toLinearMap.restrictScalars Qp) ∘ₗ LinearMap.compLeft r (Fin k)

theorem ret_apply (r : E' →ₗ[Qp] E) (b : Module.Basis (Fin k) E V) (w : Fin k → E') :
    ret r b w = ∑ i, r (w i) • b i := by
  simp [ret, Module.Basis.equivFun_symm_apply]

theorem repr_ret (r : E' →ₗ[Qp] E) (b : Module.Basis (Fin k) E V) (w : Fin k → E') (i : Fin k) :
    b.repr (ret r b w) i = r (w i) := by
  rw [ret_apply]; simp [Finsupp.single_apply]

theorem ret_emb (j : E →ₐ[Qp] E') (r : E' →ₗ[Qp] E) (hr : ∀ a x, r (j a * x) = a * r x) (h1 : r 1 = 1)
    (b : Module.Basis (Fin k) E V) (v : V) : ret r b (emb j b v) = v := by
  refine b.ext_elem fun i => ?_
  have := hr (b.repr v i) 1
  rw [mul_one, h1, mul_one] at this
  rw [repr_ret, emb_apply, this]

theorem emb_map (j : E →ₐ[Qp] E') (b : Module.Basis (Fin k) E V) (b' : Module.Basis (Fin k') E V')
    (f : V →ₗ[E] V') (v : V) :
    emb j b' (f v) = ((LinearMap.toMatrix b b' f).map j).mulVec (emb j b v) := by
  funext i
  have := congrFun (LinearMap.toMatrix_mulVec_repr b b' f v) i
  rw [emb_apply, ← this]
  simp [Matrix.mulVec, dotProduct, emb_apply]

theorem ret_map (j : E →ₐ[Qp] E') (r : E' →ₗ[Qp] E) (hr : ∀ a x, r (j a * x) = a * r x)
    (b : Module.Basis (Fin k) E V) (b' : Module.Basis (Fin k') E V')
    (f : V →ₗ[E] V') (w : Fin k → E') :
    ret r b' (((LinearMap.toMatrix b b' f).map j).mulVec w) = f (ret r b w) := by
  refine b'.ext_elem fun i => ?_
  have := congrFun (LinearMap.toMatrix_mulVec_repr b b' f (ret r b w)) i
  rw [repr_ret, ← this]
  simp [Matrix.mulVec, dotProduct, repr_ret, hr]

end Maps

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

theorem liftF_descends : ∀ (l : ℕ) [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] {K₀ K B BdR : Type} [Field K₀] [Field K] [Algebra ℚ_[l] K₀] [Algebra ℚ_[l] K] [Algebra K₀ K] [IsScalarTower ℚ_[l] K₀ K] [CommRing B] [CommRing BdR] [Algebra ℚ_[l] B] [Algebra K₀ B] [IsScalarTower ℚ_[l] K₀ B] [Algebra ℚ_[l] BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower ℚ_[l] K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower ℚ_[l] K₀ BdR] (PD : PeriodData G ℚ_[l] K₀ K B BdR) (LL LL' : FinExt l) (hL : LL.1 ≤ LL'.1) (T₁ T₂ : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)) (k₁ k₂ : ℕ) (b₁ : Module.Basis (Fin k₁) ↥LL.1 T₁.V) (b₂ : Module.Basis (Fin k₂) ↥LL.1 T₂.V) (hb₁ : IsLatBasis T₁ b₁) (hb₂ : IsLatBasis T₂ b₂) (F : LatHom T₁.L T₂.L) (r : ↥LL'.1 →ₗ[ℚ_[l]] ↥LL.1), (∀ a x, r (incl hL a * x) = a * r x) → r 1 = 1 → (∀ x ∈ OL LL', r x ∈ OL LL) → Continuous r → ∀ e : ℕ, (extHom hL hb₁ hb₂ F).LiftF PD e → F.LiftF PD e := by
  intro l _ G _ _ K₀ K B BdR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PD LL LL' hL T₁ T₂ k₁ k₂ b₁ b₂ hb₁ hb₂ F r hr h1
    hint hrc e h
  have hincl : Continuous (incl hL) := continuous_subtype_val.subtype_mk _
  have retT : ∀ {T : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)} {k : ℕ} {b : Module.Basis (Fin k) ↥LL.1 T.V},
      IsLatBasis T b → ∀ x ∈ intVec LL' k, ret r b x ∈ T.L.T := by
    intro T k b hb x hx
    rw [ret_apply]
    refine Submodule.sum_mem _ fun i _ => ?_
    have := T.L.T.smul_mem (⟨r (x i), hint _ (hx i)⟩ : ↥(OL LL)) (hb.1 i)
    rwa [← algebraMap_smul ↥LL.1] at this
  refine liftF_of_retract PD F (extHom hL hb₁ hb₂ F) (emb (incl hL) b₂) (ret r b₁) (ret r b₂)
    (fun g x => emb_map (incl hL) b₂ b₂ (T₂.ρ g) x) ?_ ?_
    (fun g x => ret_map (incl hL) r hr b₁ b₁ (T₁.ρ g) x) ?_ (retT hb₁)
    (fun g x => ret_map (incl hL) r hr b₂ b₂ (T₂.ρ g) x) (retT hb₂)
    (ret_emb (incl hL) r hr h1 b₂) (fun x => ret_map (incl hL) r hr b₁ b₂ F.f x) e h
  · exact continuous_pi fun i => hincl.comp (IsModuleTopology.continuous_of_linearMap (b₂.coord i))
  · intro x hx i
    exact incl_integral hL (hb₂.2 x hx i)
  · have hc : Continuous (b₁.equivFun.symm.toLinearMap) := IsModuleTopology.continuous_of_linearMap _
    exact hc.comp (continuous_pi fun i => hrc.comp (continuous_apply i))

end GlobalTheory.CoefDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalCupPairingReducedCocyclesStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.Published.PoitouTate GlobalTheory.ResSel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_cup_pairing_reduced_cocycles : LocalTateDuality → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), GalHyp bkP i s → ∀ (K : Type) [Field K] [Algebra (X.O0 i) K] [TopologicalSpace K] [DiscreteTopology K], IsRes i K → ∀ ρ, IsDual i s ρ → ∀ v ∈ placesOver D.host.E (X.l i), ∀ (x : Z1 ((red i K (Tgl i s)).comp (DecV N v).subtype)) (y : Z1 ((red i K ρ).comp (DecV N v).subtype)), Submodule.Quotient.mk x ∈ bkOn bkP i (Tgl i s) (1 : GE N →* Kˣ) K v → Submodule.Quotient.mk y ∈ bkOn bkP i ρ (1 : GE N →* Kˣ) K v → ∀ (lam : K →+ ZMod (X.l i ^ 1)) (w : Z2 (muLoc D.host.E (X.l i) 1 (N.plOm.1 v))), (∀ g h : ↥(DecV N v), w.1 (g, h) = lam (x.1 g ⬝ᵥ red i K ρ g (y.1 h))) → (Submodule.Quotient.mk w : H2 (muLoc D.host.E (X.l i) 1 (N.plOm.1 v))) = 0 := by
  first | exact @GlobalTheory.CupAbove.cup_eq_zero_above | exact GlobalTheory.CupAbove.cup_eq_zero_above | (intros; apply GlobalTheory.CupAbove.cup_eq_zero_above <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalCompatibilityAtTypesStatement
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_global_compatibility_at_types : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), SumRepresentations.ConclusionG5 D → HG D.nd D.naut i → GoodR D.nd i r → TruncatedSeriesCountingIdentities.TameGeneratorConditions (D := D) i → TameCharacterConditions D i → (∀ w ∈ D.nd.S i, (∃ k, w ∈ placesOver D.host.E (D.host.g k)) → (∀ x, ∃ P, D.naut.ptV i P = some x ∧ D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) (r x)) w = D.naut.lpTw (D.naut.locV i P w) ((1 - (D.R.nV : ℝ)) / 2)) ∧ ∀ P : D.naut.AV i, ∀ σ ∈ wildSet D.nd (D.nd.plOm.1 w), D.naut.inePol (D.naut.locV i P w) σ = (Polynomial.X - 1) ^ D.R.nV) → PairedCharacterCondition.SetSQ i r := by
  first | exact @GlobalTheory.WildSetSQ.main | exact GlobalTheory.WildSetSQ.main | (intros; apply GlobalTheory.WildSetSQ.main <;> assumption)
end

