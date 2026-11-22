import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0083
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0060
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsTwistBasisOffPrime
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGeneratorOfBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0024
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0084
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0085
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFourierJacobiExpansionOverField
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.UU.ExpTotal
open GlobalTheory.TwistLoc (gc gc_mul)

section General
variable {X X' W Y Z : Scheme.{0}}

theorem gs_scal {R : Type} [CommRing R] (p : Y ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ Y) (z : Z) (a : R) :
    gs r z ⊤ (scal p a) = gc (r ≫ p) z a := gs_pull r p z ⊤ trivial _

theorem gc_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (q : Z ⟶ Spec (CommRingCat.of S)) (z : Z) (a : R) :
    gc (q ≫ Spec.map (CommRingCat.ofHom f)) z a = gc q z (f a) := by
  refine (gs_pull q _ z ⊤ trivial _).symm.trans (congrArg (gs q z ⊤) ?_)
  exact (congrArg (fun g => g.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))).symm

theorem exists_comb {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} {n : ℕ} (c : Fin n → Γ(Y, ⊤))
    (t : Fin n → LB.Sec (LB.LinComb L φ ε)) : ∃ s : LB.Sec (LB.LinComb L φ ε),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J → sval s r z J = ∑ i, gs r z ⊤ (c i) * sval (t i) r z J :=
  ⟨⟨fun j => ∑ i, (IndivisibleSection.smulSec (c i) (t i)).f j, fun i j => by
    rw [map_sum, map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => (IndivisibleSection.smulSec (c l) (t l)).compat i j⟩,
    fun Z r z J hJ => DVR.SectionScalarValuation.sval_lin c t (fun _ => rfl) r z hJ⟩

theorem exists_inv {L : LB X} {L' : LB X'} {F : W ⟶ X} {F' : W ⟶ X'}
    (w : LB.Iso (L'.pull F') (L.pull F)) (hw : w.IsGen) : ∃ v : LB.Iso (L.pull F) (L'.pull F'), v.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ W) (z : Z) (i : L.ι) (j : L'.ι), F (r z) ∈ L.U i → F' (r z) ∈ L'.U j →
        gw v r z j (fun _ => i) = (gw w r z i (fun _ => j))⁻¹ := by
  let v : LB.Iso (L.pull F) (L'.pull F') := ⟨fun p => (res (le_inf inf_le_right inf_le_left :
    (L'.pull F').U p.1 ⊓ (L.pull F).U p.2 ≤ (L.pull F).U p.2 ⊓ (L'.pull F').U p.1) (w.s (p.2, p.1)))⁻¹⟩
  have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ W) (z : Z) (i : L.ι) (j : L'.ι), F (r z) ∈ L.U i → F' (r z) ∈ L'.U j →
      gw v r z j (fun _ => i) = (gw w r z i (fun _ => j))⁻¹ := fun Z r z i j hi hj =>
    (map_inv _ _).trans (congrArg (·⁻¹) (gm_res r z _
      (show r z ∈ (L'.pull F').U (fun _ => j) ⊓ (L.pull F).U (fun _ => i) from ⟨mem_pull.2 hj, mem_pull.2 hi⟩) _))
  refine ⟨v, (isGen_iff v).2 fun Z r z j j' i i' hj hj' hi hi' => ?_, hv⟩
  have e := (isGen_iff w).1 hw Z r z (i PUnit.unit) (i' PUnit.unit) (fun _ => j) (fun _ => j') (mem_pull.1 hi)
    (mem_pull.1 hi') (mem_pull.2 hj) (mem_pull.2 hj')
  rw [gm_pull_g L' F' r z (fun _ => j) (fun _ => j') (mem_pull.2 hj) (mem_pull.2 hj')] at e
  refine (hv Z r z (i PUnit.unit) j (mem_pull.1 hi) hj).trans ?_
  rw [e, gm_pull_g L F r z i i' hi hi']
  refine Eq.trans ?_ (congrArg _ (hv Z r z (i' PUnit.unit) j' (mem_pull.1 hi') hj')).symm
  rw [mul_inv, mul_inv, inv_inv, mul_comm _⁻¹]

end General

theorem exists_span (hS : SecBaseChangeSt) {K : Type} [Field K] (P : PolAV (Spec (CommRingCat.of K))) (n : ℕ)
    (hn : 1 ≤ n) (F : Type) [Field F] (q : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of K))
    (s : LB.Sec (LB.LinComb P.L (fun _ : Fin 1 => (snd (Over.mk q) P.A).left) (fun _ => (n : ℤ)))) :
    ∃ (m : ℕ) (c : Fin m → F) (a : Fin m → LB.Sec (LB.LinComb P.L (fun _ : Fin 1 => 𝟙 P.A.left) (fun _ => (n : ℤ)))),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (Over.mk q ⊗ P.A).left) (z : Z) (J), Good P.L z J →
        sval s r z J = ∑ i, gc (R := F) (r ≫ (fst (Over.mk q) P.A).left) z (c i) *
          sval (a i) (r ≫ (snd (Over.mk q) P.A).left) z J := by
  obtain ⟨U, hU, b, hb⟩ := hS (Spec (CommRingCat.of K)) P n hn (IsLocalRing.closedPoint K)
  obtain rfl : U = ⊤ := DVR.eq_top_of_closedPoint_mem U hU
  have hi : (Spec (CommRingCat.of K)).topIso.inv ≫
      (overRes (T := baseOver (Spec (CommRingCat.of K))) ⊤).hom = 𝟙 _ :=
    (congrArg (_ ≫ ·) (Category.comp_id _)).trans (Spec (CommRingCat.of K)).topIso.inv_hom_id
  have hi' : (overRes (T := baseOver (Spec (CommRingCat.of K))) ⊤).hom ≫ (Spec (CommRingCat.of K)).topIso.inv
      = 𝟙 _ :=
    (congrArg (· ≫ _) (Category.comp_id _)).trans (Spec (CommRingCat.of K)).topIso.hom_inv_id
  obtain ⟨t, rfl⟩ : ∃ t : Spec (CommRingCat.of F) ⟶ (overRes (T := baseOver (Spec (CommRingCat.of K))) ⊤).left,
      t ≫ (overRes (T := baseOver (Spec (CommRingCat.of K))) ⊤).hom = q :=
    ⟨q ≫ (Spec (CommRingCat.of K)).topIso.inv, (Category.assoc _ _ _).trans
      ((congrArg (q ≫ ·) hi).trans (Category.comp_id q))⟩
  let T₀ := overRes (T := baseOver (Spec (CommRingCat.of K))) ⊤
  let e : P.A ⟶ T₀ ⊗ P.A := lift (Over.homMk (P.A.hom ≫ (Spec (CommRingCat.of K)).topIso.inv)
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hi).trans (Category.comp_id _)))) (𝟙 _)
  have he : snd (baseAt t) P.A ≫ e = homAt t ▷ P.A := by
    refine CartesianMonoidalCategory.hom_ext _ _ (Over.OverMorphism.ext ?_) ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (lift_snd _ _)).trans
      ((Category.comp_id _).trans (whiskerRight_snd (homAt t) P.A).symm)))
    have : IsIso T₀.hom := ⟨_, hi', hi⟩
    rw [← cancel_mono T₀.hom, Over.w, Over.w]
  choose a ha using fun i => PullSec.exists_pullSec P.isLB (φ' := fun _ : Fin 1 => 𝟙 P.A.left) e.left
    (fun _ => (congrArg CommaMorphism.left (lift_snd _ _ : e ≫ snd _ _ = _)).symm) (b i)
  choose b' hb' using fun i => IndivisibleSection.exists_pull_chart (K := Fin 1) (b i) (homAt t ▷ P.A).left
      (fun _ => (snd (baseAt t) P.A).left)
      (fun _ => congrArg CommaMorphism.left (whiskerRight_snd (homAt t) P.A))
  have hsp := (hb F t b' fun i j => hb' i j _).2
  obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun _).1
    (hsp.ge (Submodule.mem_top (x := SecM.ofSec P.A s)))
  choose c hc using fun i => (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 (d i)
  refine ⟨_, c, a, fun Z r z J hJ => ?_⟩
  refine (DVR.SectionScalarValuation.sval_lin (s := s) (fun i => scal (R := F) (fst (baseAt t) P.A).left (c i)) b' (fun j => ?_) r z hJ).trans
    (Finset.sum_congr rfl fun i _ => congrArg₂ (· * ·) (gs_scal _ r z _) ?_)
  · refine (congrFun (congrArg Subtype.val hd) j).symm.trans ?_
    refine (congrFun (Submodule.coe_sum _ _ _) j).trans ((Finset.sum_apply _ _ _).trans
      (Finset.sum_congr rfl fun i _ => ?_))
    rw [← hc i]
    rfl
  · have e₁ : (r ≫ (snd (baseAt t) P.A).left) ≫ e.left = r ≫ (homAt t ▷ P.A).left :=
      (Category.assoc _ _ _).trans (congrArg (r ≫ ·) (congrArg CommaMorphism.left he))
    have e₂ : (r ≫ (homAt t ▷ P.A).left) ≫ (snd T₀ P.A).left = r ≫ (snd (baseAt t) P.A).left :=
      (Category.assoc _ _ _).trans (congrArg (r ≫ ·) (congrArg CommaMorphism.left (whiskerRight_snd (homAt t) P.A)))
    refine Eq.trans ?_ (ha i Z _ z J hJ).symm
    rw [e₁, sval_of (φ := fun _ : Fin 1 => (snd T₀ P.A).left) (b i) _ z J
      (fun _ => J (r ≫ (snd (baseAt t) P.A).left)) (fun _ => congrArg J e₂)]
    have hm := hJ.mem (fun _ : Fin 1 => (snd (baseAt t) P.A).left) r
    have le := chart_le_res P.A P.L (homAt t ▷ P.A) (whiskerRight_snd (homAt t) P.A) n
      (fun _ => J (r ≫ (snd (baseAt t) P.A).left))
    exact (congrArg (gs r z _) (hb' i _ le)).trans ((gs_res r z le hm _).trans (gs_pull r (homAt t ▷ P.A).left z _ (le hm) _))

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

theorem exists_integral (U : PreU I D A G) (k : ℕ)
    (a : LB.Sec (LB.LinComb A.L (fun _ : Fin 1 => 𝟙 A.A.left) (fun _ => (k : ℤ)))) :
    ∃ t : R, t ≠ 0 ∧ ∃ σ : U.SecGT (𝟙_ _) k, ∀ (Z : Scheme.{0}) (y : Z ⟶ ((Over.pullback (jK R)).obj G).left)
      (rG : Z ⟶ (𝟙_ _ ⊗ G).left), rG ≫ (snd _ G).left = y ≫ pullback.fst G.hom (jK R) →
      ∀ (z : Z) (JA) (JG), Good A.L z JA → Good U.P.L.L z JG →
        sval σ rG z JG = gc (y ≫ pullback.fst G.hom (jK R) ≫ G.hom) z t *
          ((gw U.wA y z (JG (y ≫ pullback.fst G.hom (jK R))) (fun _ => JA (y ≫ U.gen.hom.left))).val ^ k *
            sval a (y ≫ U.gen.hom.left) z JA) := by
  have := U.semi.quasiCompact
  have := U.semi.separated
  have : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  have : QuasiSeparatedSpace G.left := quasiSeparatedSpace_of_quasiSeparated G.hom
  obtain ⟨v, hv, hvw⟩ := exists_inv U.wA U.wA_gen
  obtain ⟨s', hs'⟩ := PullSec.exists_sec_of_iso A.isLB U.P.L.isLB v hv (𝟙 _) U.gen.hom.left
    (pullback.fst G.hom (jK R) ≫ 𝟙 G.left) (𝟙 A.A.left) ((Category.id_comp _).trans (Category.comp_id _).symm)
    ((Category.id_comp _).trans (Category.comp_id _).symm) k a
  obtain ⟨t, ht, σ₀, hσ₀⟩ := TwistLoc.exists_clear_denominator (nonZeroDivisors R)
    (IsPullback.of_hasPullback G.hom (jK R)) U.P.L.isLB (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (k : ℤ)) s'
  obtain ⟨σ, hσ⟩ := PullSec.exists_pullSec U.P.L.isLB (φ' := fun _ : Fin 1 => (snd (𝟙_ _) G).left)
    (snd (𝟙_ _) G).left (fun _ => (Category.comp_id _).symm) σ₀
  refine ⟨t, nonZeroDivisors.ne_zero ht, σ, fun Z y rG e z JA JG hA hG => (hσ Z rG z JG hG).trans ?_⟩
  have mA := hA (y ≫ U.gen.hom.left)
  have mG := hG (y ≫ pullback.fst G.hom (jK R))
  rw [e, sval_of σ₀ _ z JG (fun _ => JG (y ≫ pullback.fst G.hom (jK R))) (fun _ => congrArg JG (Category.comp_id _)),
    sval_of a _ z JA (fun _ => JA (y ≫ U.gen.hom.left)) (fun _ => congrArg JA (Category.comp_id _))]
  refine (hσ₀ Z y z _ (Set.mem_iInter.2 fun _ => mG)).trans (congrArg _ ?_)
  have h := hs' Z y z _ _ mA mG
  rw [Category.comp_id y, hvw Z y z _ _ mG mA] at h
  refine Eq.trans ?_ (congrArg _ h)
  rw [← _root_.mul_assoc, ← mul_pow, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_pow, _root_.one_mul]

theorem exists_pullB (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (α : D.X)
    (f : SecBT D (𝟙_ _) k α) : ∃ s : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k)),
      ∀ (Z : Scheme.{0}) (rF : Z ⟶ (DegPre.BF D F).left) (rB : Z ⟶ (𝟙_ _ ⊗ D.P.A).left),
        rB ≫ (snd _ D.P.A).left = rF ≫ (DegPre.prB D F).left → ∀ (z : Z) (J), Good D.P.L z J →
          sval s rF z J = sval f rB z J := by
  let φ := toUnit (TF (R := R) F)
  have a₀ : snd (TF (R := R) F) D.P.A = φ ▷ D.P.A ≫ snd (𝟙_ _) D.P.A := (whiskerRight_snd _ _).symm
  have hc : ∀ i : Fin 4, DegPre.famφ D F α i = (φ ▷ D.P.A).left ≫ famφT D (𝟙_ _) α i := fun i => by
    have u : φ ▷ D.P.A ≫ toUnit (𝟙_ _ ⊗ D.P.A) = toUnit _ := toUnit_unique _ _
    have a₂ : ∀ c : 𝟙_ _ ⟶ D.P.A, toUnit (DegPre.BF D F) ≫ c = φ ▷ D.P.A ≫ toUnit (𝟙_ _ ⊗ D.P.A) ≫ c := fun c => by
      rw [← Category.assoc, u]
    fin_cases i
    · exact congrArg (fun q => q.left) a₀
    · exact congrArg (fun q => q.left) ((congrArg₂ (· * ·) a₀ (a₂ (D.c α))).trans (MonObj.comp_mul _ _ _).symm)
    · exact congrArg (fun q => q.left) (a₂ (D.c α))
    · exact congrArg (fun q => q.left) (a₂ η[D.P.A])
  obtain ⟨s, hs⟩ := PullSec.exists_pullSec D.P.isLB (φ ▷ D.P.A).left hc f
  refine ⟨s, fun Z rF rB e z J hJ => (hs Z rF z J hJ).trans (congrArg (sval f · z J) ?_)⟩
  have : IsIso (snd (𝟙_ _) D.P.A) := by rw [← leftUnitor_hom]; infer_instance
  have : IsIso (snd (𝟙_ _) D.P.A).left := inferInstanceAs (IsIso ((Over.forget _).map (snd (𝟙_ _) D.P.A)))
  rw [← cancel_mono (snd (𝟙_ _) D.P.A).left, e]
  exact (Category.assoc _ _ _).trans (congrArg (rF ≫ ·) (congrArg CommaMorphism.left a₀).symm)

theorem exists_expF (hS : SecBaseChangeSt) (U : PreU I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F]
    (k : ℕ) (hk : 1 ≤ k) (hb : ∀ σ, ∃ f, U.ExpT (𝟙_ _) k σ f)
    (t : LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := R) F))) : ∃ s, U.ExpF F k t s := by
  obtain ⟨n, c, a, ha⟩ := exists_span hS A k hk F (jFK (R := R) F) t
  choose d hd σ hσ using fun i => exists_integral U k (a i)
  choose f hf using fun i => hb (σ i)
  choose g hg using fun i α => exists_pullB D F k α (f i α)
  let ψ : R →+* F := (algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))
  have hψ : ∀ i, ψ (d i) ≠ 0 := fun i => (map_ne_zero (algebraMap (FractionRing R) F)).2
    ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 (hd i))
  choose s hs using fun α => exists_comb
    (fun i => scal (R := F) (fst (TF (R := R) F) D.P.A).left (c i * (ψ (d i))⁻¹)) (fun i => g i α)
  refine ⟨s, n, fun i => c i * (ψ (d i))⁻¹, σ, f, hf, fun Z rA y rG e₁ e₂ z JA JG hA hG => ?_,
    fun α Z rF rB e z J hJ => (hs α Z rF z J hJ).trans
      (Finset.sum_congr rfl fun i _ => congrArg _ (hg i α Z rF rB e z J hJ))⟩
  refine (congrArg _ (ha Z rA z JA hA)).trans ((Finset.mul_sum _ _ _).trans (Finset.sum_congr rfl fun i _ => ?_))
  have e₃ : y ≫ pullback.fst G.hom (jK R) ≫ G.hom =
      ((rA ≫ (fst (TFK (R := R) F) A.A).left) ≫ jFK (R := R) F) ≫ jK R := by
    have w₁ : U.gen.hom.left ≫ A.A.hom = pullback.snd G.hom (jK R) := Over.w U.gen.hom
    have w₂ : (fst (TFK (R := R) F) A.A).left ≫ jFK (R := R) F = (snd (TFK (R := R) F) A.A).left ≫ A.A.hom :=
      (Over.w (fst (TFK (R := R) F) A.A)).trans (Over.w (snd (TFK (R := R) F) A.A)).symm
    refine (congrArg (y ≫ ·) pullback.condition).trans ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ jK R) ?_))
    exact (congrArg (y ≫ ·) w₁.symm).trans ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ A.A.hom) e₁.symm).trans
      ((Category.assoc _ _ _).trans ((congrArg (rA ≫ ·) w₂.symm).trans (Category.assoc _ _ _).symm))))
  have e₄ : gc (y ≫ pullback.fst G.hom (jK R) ≫ G.hom) z (d i) =
      gc (R := F) (rA ≫ (fst (TFK (R := R) F) A.A).left) z (ψ (d i)) :=
    (congrArg (gc · z (d i)) e₃).trans ((gc_map _ _ z _).trans (gc_map _ _ z _))
  refine Eq.trans ?_ (congrArg₂ (· * ·) (gs_scal (R := F) _ rA z _) (hσ i Z y rG e₂ z JA JG hA hG)).symm
  rw [e₄, ← _root_.mul_assoc (gc _ _ _) (gc _ _ _), ← gc_mul, inv_mul_cancel_right₀ (hψ i)]
  exact (mul_left_comm _ _ _).trans (congrArg (fun q => _ * (_ * sval (a i) q z JA)) e₁)

theorem expF_total : Laws → Laws2 → (AllPre fun {V} _ _ _ {_} {_} {_} _ _ U => ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k → ∀ t, ∃ s, U.ExpF F k t s) :=
  fun h h₂ V _ _ _ hV D A G _ _ U F _ _ k hk t =>
    exists_expF h.secBaseChange U F k hk (GlobalTheory.T.exists_expansion_section_lineBundle_power h h₂ V hV D A G U k hk) t

end GlobalTheory.UU.ExpTotal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.HasBasisOfBasis
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GenericSectionBasis

section Calc

variable {F : Type} [CommRing F] {X Y Y' Z : Scheme.{0}} {n : ℕ}

def IsComb {M : LB Y} (p : Y ⟶ Sp F) (b : Fin n → LB.Sec M) (c : Fin n → F) (s : LB.Sec M) : Prop :=
  ∀ j, s.f j = ∑ i, resTop _ (scal p (c i)) * (b i).f j

def HasBasis (M : LB Y) (p : Y ⟶ Sp F) (n : ℕ) : Prop :=
  ∃ b : Fin n → LB.Sec M, ∀ s : LB.Sec M, ∃! c : Fin n → F, IsComb p b c s

theorem exists_comb {M : LB Y} (p : Y ⟶ Sp F) (b : Fin n → LB.Sec M) (c : Fin n → F) :
    ∃ s : LB.Sec M, IsComb p b c s :=
  ⟨⟨fun j => ∑ i, resTop _ (scal p (c i)) * (b i).f j, fun j j' => by
    rw [map_sum, map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => (SecOps.secScale (scal p (c i)) (b i)).compat j j'⟩, fun _ => rfl⟩

theorem gs_comb {M : LB Y} (p : Y ⟶ Sp F) (b : Fin n → LB.Sec M) (c : Fin n → F) (r : Z ⟶ Y) (z : Z) (j : M.ι)
    (hz : r z ∈ M.U j) :
    gs r z (M.U j) (∑ i, resTop _ (scal p (c i)) * (b i).f j) =
      ∑ i, cst (r ≫ p) z (c i) * gs r z (M.U j) ((b i).f j) := by
  rw [gs_eq r z _ hz, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← gs_eq r z _ hz, gs_mul r z _ hz, GlobalTheory.IndivisibleSection.gs_scal p r z _ hz]

theorem HasBasis.transfer {A : LB Y'} {B : LB Y} (hA : A.IsLB) (hB : B.IsLB) (σ : Y' ⟶ Y) (τ : Y ⟶ Y')
    (h₁ : τ ≫ σ = 𝟙 Y) (p : Y ⟶ Sp F) (p' : Y' ⟶ Sp F) (hp : σ ≫ p = p')
    (u : ∀ (Z : Scheme.{0}) (_ : Z ⟶ Y') (z : Z), A.ι → B.ι → (Z.presheaf.stalk z)ˣ)
    (Rel : LB.Sec A → LB.Sec B → Prop)
    (hRel : ∀ s t, Rel s t → ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (a : A.ι) (b : B.ι), r z ∈ A.U a →
      (r ≫ σ) z ∈ B.U b → gs r z (A.U a) (s.f a) = (u Z r z a b).val * gs (r ≫ σ) z (B.U b) (t.f b))
    (hl : ∀ t, ∃ s, Rel s t) (hr : ∀ s, ∃ t, Rel s t) (H : HasBasis B p n) : HasBasis A p' n := by
  obtain ⟨β, hβ⟩ := H
  choose β' hβ' using fun i => hl (β i)
  refine ⟨β', fun s => ?_⟩
  obtain ⟨t, ht⟩ := hr s
  have key : ∀ c, IsComb p' β' c s ↔ IsComb p β c t := fun c => by
    constructor
    · intro h j
      refine fn_ext fun y hy => ?_
      obtain ⟨a, ha⟩ := exists_chart hA (τ y)
      have hy' : (τ ≫ σ) y ∈ B.U j := by rw [h₁]; exact hy
      have e := hRel s t ht Y τ y a j ha hy'
      rw [h a, gs_comb p' β' c τ y a ha] at e
      simp only [fun i => hRel _ _ (hβ' i) Y τ y a j ha hy', h₁] at e
      rw [gs_comb p β c (𝟙 Y) y j hy, ← (u Y τ y a j).mul_right_inj, ← e, Finset.mul_sum, ← hp,
        ← Category.assoc, h₁]
      exact Finset.sum_congr rfl fun i _ => mul_left_comm _ _ _
    · intro h a
      refine fn_ext fun y hy => ?_
      obtain ⟨j, hj⟩ := exists_chart hB (σ y)
      have hy' : (𝟙 Y' ≫ σ) y ∈ B.U j := hj
      rw [hRel s t ht Y' (𝟙 Y') y a j hy hy', h j, gs_comb p β c _ y j hy', gs_comb p' β' c (𝟙 Y') y a hy,
        Finset.mul_sum, ← hp, Category.assoc]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hRel _ _ (hβ' i) Y' (𝟙 Y') y a j hy hy']
      exact mul_left_comm _ _ _
  simp only [key]
  exact hβ t

theorem exists_inv_iso {A B : LB X} (w : LB.Iso A B) (hw : w.IsGen) : ∃ w' : LB.Iso B A, w'.IsGen ∧
    ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (a : A.ι) (b : B.ι), r z ∈ A.U a ⊓ B.U b →
      gm r z ((LB.div A B).U (a, b)) (w'.s (a, b)) = (gm r z ((LB.div B A).U (b, a)) (w.s (b, a)))⁻¹ := by
  have le : ∀ p : A.ι × B.ι, A.U p.1 ⊓ B.U p.2 ≤ B.U p.2 ⊓ A.U p.1 := fun p y hy => ⟨hy.2, hy.1⟩
  refine ⟨⟨fun p => (res (le p) (w.s (p.2, p.1)))⁻¹⟩, fun p q => unit_ext fun y hy => ?_,
    fun Z r z a b hz => (map_inv _ _).trans (congrArg (·⁻¹) (gm_res r z (le (a, b)) hz _))⟩
  have hm : (𝟙 X : X ⟶ X) y ∈ B.U p.2 ⊓ A.U p.1 ⊓ (B.U q.2 ⊓ A.U q.1) := ⟨le p hy.1, le q hy.2⟩
  have e := congrArg (gm (𝟙 X) y (B.U p.2 ⊓ A.U p.1 ⊓ (B.U q.2 ⊓ A.U q.1))) (hw (p.2, p.1) (q.2, q.1))
  have e' := (gm_res _ y _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_div A B (𝟙 X) y (p.2, p.1) (q.2, q.1) hm) (gm_res _ y _ hm _))))
  have v : ∀ p : A.ι × B.ι, y ∈ A.U p.1 ⊓ B.U p.2 → gm (𝟙 X) y (A.U p.1 ⊓ B.U p.2) (res (le p) (w.s (p.2, p.1)))⁻¹ =
      (gm (𝟙 X) y (B.U p.2 ⊓ A.U p.1) (w.s (p.2, p.1)))⁻¹ := fun p hp =>
    (map_inv _ _).trans (congrArg (·⁻¹) (gm_res _ y _ hp _))
  refine ((gm_res _ y _ hy _).trans ((v p hy.1).trans (congrArg (·⁻¹) e'))).trans (Eq.symm ?_)
  refine ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_div B A (𝟙 X) y p q hy)
    ((gm_res _ y _ hy _).trans (v q hy.2)))).trans ?_
  rw [mul_inv, mul_inv, inv_inv, mul_comm (gm (𝟙 X) y _ (A.g p.1 q.1))]
  rfl

theorem HasBasis.of_iso {A B : LB Y} (hA : A.IsLB) (hB : B.IsLB) (h : LBIso A B) {p : Y ⟶ Sp F}
    (H : HasBasis B p n) : HasBasis A p n := by
  obtain ⟨w, hw⟩ := h
  obtain ⟨w', hw', e⟩ := exists_inv_iso w hw
  refine H.transfer hA hB (𝟙 Y) (𝟙 Y) (Category.id_comp _) p p (Category.id_comp _)
    (fun Z r z a b => (gm r z ((LB.div B A).U (b, a)) (w.s (b, a)))⁻¹) _ (fun _ _ h => h)
    (fun t => ⟨secOfIso t hw hA hB, fun Z r z a b ha hb => ?_⟩)
    (fun s => ⟨secOfIso s hw' hB hA, fun Z r z a b ha hb => ?_⟩)
  · rw [Category.comp_id] at hb ⊢
    exact GlobalTheory.GenericGenerated.gs_secOfIso w t hw hA hB a b r z ⟨ha, hb⟩
  · rw [Category.comp_id] at hb ⊢
    rw [GlobalTheory.GenericGenerated.gs_secOfIso w' s hw' hB hA b a r z ⟨hb, ha⟩, e Z r z a b ⟨ha, hb⟩, inv_inv,
      Units.inv_mul_cancel_left]

theorem exists_pull_gs {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y) (φ' : K → (Y' ⟶ X)) (e : ∀ k, h ≫ φ k = φ' k) :
    ∃ s' : LB.Sec (LB.LinComb L φ' ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (j : K → L.ι),
      r z ∈ LB.wchart L φ' j →
      gs r z (LB.wchart L φ' j) (s'.f j) = gs (r ≫ h) z (LB.wchart L φ j) (s.f j) := by
  obtain ⟨s', hs'⟩ := GlobalTheory.IndivisibleSection.exists_pull_chart s h φ' e
  refine ⟨s', fun Z r z j hz => ?_⟩
  have le : LB.wchart L φ' j ≤ h ⁻¹ᵁ LB.wchart L φ j := fun y hy => Set.mem_iInter.2 fun k => by
    have := Set.mem_iInter.1 hy k
    rw [← e] at this
    exact this
  rw [hs' j le]
  exact (gs_res r z le hz _).trans (gs_pull r h z _ (le hz) _)

theorem HasBasis.pull {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {φ' : K → (Y' ⟶ X)}
    {ε : K → ℤ} (σ : Y' ⟶ Y) (τ : Y ⟶ Y') (h₁ : τ ≫ σ = 𝟙 Y) (h₂ : σ ≫ τ = 𝟙 Y') (e : ∀ k, σ ≫ φ k = φ' k)
    (p : Y ⟶ Sp F) (p' : Y' ⟶ Sp F) (hp : σ ≫ p = p') (H : HasBasis (LB.LinComb L φ ε) p n) :
    HasBasis (LB.LinComb L φ' ε) p' n := by
  have e' : ∀ k, τ ≫ φ' k = φ k := fun k => by rw [← e, ← Category.assoc, h₁, Category.id_comp]
  have mem : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (b : K → L.ι), (r ≫ σ) z ∈ LB.wchart L φ b →
      r z ∈ LB.wchart L φ' b := fun Z r z b hb => Set.mem_iInter.2 fun k => by
    have := Set.mem_iInter.1 hb k
    rw [← e]
    exact this
  refine H.transfer (linComb_isLB L hL _ _) (linComb_isLB L hL _ _) σ τ h₁ p p' hp
    (fun Z r z a b => trF φ' ε r z a b) _ (fun _ _ h => h) (fun t => ?_) (fun s => ?_)
  · obtain ⟨s, hs⟩ := exists_pull_gs t σ φ' e
    exact ⟨s, fun Z r z a b ha hb => (sec_trans s r z ha (mem Z r z b hb)).trans
      (congrArg _ (hs Z r z b (mem Z r z b hb)))⟩
  · obtain ⟨t, ht⟩ := exists_pull_gs s τ φ e'
    refine ⟨t, fun Z r z a b ha hb => (sec_trans s r z ha (mem Z r z b hb)).trans (congrArg _ ?_)⟩
    refine Eq.trans ?_ (ht Z (r ≫ σ) z b hb).symm
    rw [Category.assoc, h₂, Category.comp_id]

end Calc

section Field

variable {F : Type} [Field F] (P : PolAV (Spec (CommRingCat.of F))) (k : ℕ)

theorem hasBasis_of_basis (q : Sp F ⟶ Sp F) (hq : q = 𝟙 _) {n : ℕ}
    (β : Fin n → LB.Sec (LPow P.A P.L k (Over.mk q)))
    (hli : LinearIndependent Γ((Over.mk q).left, ⊤) (fun i => (SecM.ofSec P.A (β i) : SecM P.A P.L k (Over.mk q))))
    (hsp : Submodule.span Γ((Over.mk q).left, ⊤)
      (Set.range fun i => (SecM.ofSec P.A (β i) : SecM P.A P.L k (Over.mk q))) = ⊤) :
    HasBasis (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => (k : ℤ))) P.A.hom n := by
  subst hq
  let u : P.A ⟶ Over.mk (𝟙 (Sp F)) := Over.homMk P.A.hom (Category.comp_id _)
  have hw : (snd (Over.mk (𝟙 (Sp F))) P.A).left ≫ P.A.hom = (fst (Over.mk (𝟙 (Sp F))) P.A).left :=
    (Over.w (snd (Over.mk (𝟙 (Sp F))) P.A)).trans
      ((Over.w (fst (Over.mk (𝟙 (Sp F))) P.A)).symm.trans (Category.comp_id _))
  have hu : snd (Over.mk (𝟙 (Sp F))) P.A ≫ u = fst (Over.mk (𝟙 (Sp F))) P.A := Over.OverMorphism.ext hw
  have e₁ : lift u (𝟙 P.A) ≫ snd (Over.mk (𝟙 (Sp F))) P.A = 𝟙 _ := lift_snd _ _
  have e₂ : snd (Over.mk (𝟙 (Sp F))) P.A ≫ lift u (𝟙 P.A) = 𝟙 _ := by
    rw [comp_lift, hu, Category.comp_id, lift_fst_snd]
  have e₃ : lift u (𝟙 P.A) ≫ fst (Over.mk (𝟙 (Sp F))) P.A = u := lift_fst _ _
  refine HasBasis.pull P.isLB (φ := fun _ : Fin 1 => (snd (Over.mk (𝟙 (Sp F))) P.A).left)
    (lift u (𝟙 P.A)).left (snd (Over.mk (𝟙 (Sp F))) P.A).left
    (congrArg CommaMorphism.left e₂) (congrArg CommaMorphism.left e₁) (fun _ => congrArg CommaMorphism.left e₁)
    (fst (Over.mk (𝟙 (Sp F))) P.A).left _ (congrArg CommaMorphism.left e₃) ⟨β, fun s => ?_⟩
  have bij := ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv
  have key : ∀ c : Fin n → F, IsComb (fst (Over.mk (𝟙 (Sp F))) P.A).left β c s ↔
      ∑ i, (show Γ((Over.mk (𝟙 (Sp F))).left, ⊤) from (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (c i)) •
        (SecM.ofSec P.A (β i) : SecM P.A P.L k (Over.mk (𝟙 (Sp F)))) = SecM.ofSec P.A s := fun c => by
    rw [Subtype.ext_iff, Submodule.coe_sum, funext_iff]
    refine forall_congr' fun j => ?_
    rw [Finset.sum_apply]
    exact eq_comm
  obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 (hsp.ge (Submodule.mem_top (x := SecM.ofSec P.A s)))
  choose c hc using fun i => bij.2 (r i)
  obtain rfl : (fun i => (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (c i)) = r := funext hc
  refine ⟨c, (key c).2 hr, fun c' hc' => funext fun i => bij.1 ?_⟩
  exact Fintype.linearIndependent_iffₛ.1 hli _ _ (((key c').1 hc').trans hr.symm) i

theorem hasBasis_field (hS : SecBaseChangeSt) (hk : 1 ≤ k) :
    HasBasis (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => (k : ℤ))) P.A.hom (k ^ P.g) := by
  obtain ⟨U, hU, b, hb⟩ := hS (Spec (CommRingCat.of F)) P k hk (IsLocalRing.closedPoint F)
  obtain rfl : U = ⊤ := eq_top_of_closedPoint_mem U hU
  let t : Spec (CommRingCat.of F) ⟶ (overRes (T := baseOver (Spec (CommRingCat.of F))) ⊤).left :=
    (Spec (CommRingCat.of F)).topIso.inv
  have ht : t ≫ (overRes (T := baseOver (Spec (CommRingCat.of F))) ⊤).hom = 𝟙 _ := by
    show (Spec (CommRingCat.of F)).topIso.inv ≫ (Scheme.Opens.ι ⊤ ≫ 𝟙 _) = 𝟙 _
    rw [Category.comp_id]
    exact (Spec (CommRingCat.of F)).topIso.inv_hom_id
  have pull : ∀ i, ∃ b' : LB.Sec (LPow P.A P.L k (baseAt t)),
      IsPullSec P.A P.L k (homAt t ▷ P.A) (whiskerRight_snd (homAt t) P.A) (b i) b' := fun i => by
    obtain ⟨s', hs'⟩ := GlobalTheory.IndivisibleSection.exists_pull_chart (K := Fin 1) (b i) (homAt t ▷ P.A).left
      (fun _ => (snd (baseAt t) P.A).left)
      (fun _ => congrArg CommaMorphism.left (whiskerRight_snd (homAt t) P.A))
    exact ⟨s', fun j => hs' j _⟩
  choose b' hb' using pull
  obtain ⟨hli, hsp⟩ := hb F t b' hb'
  exact hasBasis_of_basis P k _ ht b' hli hsp

end Field

theorem iso_pow {X X' Y : Scheme.{0}} {L : LB X} {M : LB X'}
    (g : Y ⟶ X) (gi : X ⟶ Y) (e₁ : gi ≫ g = 𝟙 X) (e₂ : g ≫ gi = 𝟙 Y) (p : Y ⟶ X')
    (H : LBIso (L.pull g) (M.pull p)) (k : ℤ) :
    LBIso (LB.LinComb M (K := Fin 1) (fun _ => p) (fun _ => k))
      (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => k)) := by
  obtain ⟨w, hw⟩ : LBIso L (M.pull (gi ≫ p)) :=
    LBIso.chartPull (chartPullSec L g gi e₁)
      (chartPullSame M (fun _ : PUnit => gi ≫ p) (fun _ => p) (fun _ => 1) gi fun _ => rfl) H
  have H₂ := iso_linComb ((isGen_iff w).1 hw) (fun _ : Fin 1 => g) (fun _ => k)
  have ep : (fun _ : Fin 1 => g ≫ gi ≫ p) = fun _ => p := by
    funext _; rw [← Category.assoc, e₂, Category.id_comp]
  rw [ep] at H₂
  exact LBIso.symm H₂

theorem exists_secK_basis : SecBaseChangeSt → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (k : ℕ), 1 ≤ k → ∃ b : Fin (k ^ A.g) → U.SecK k, (∀ c : Fin (k ^ A.g) → FractionRing R, ∃ s : U.SecK k, (∀ j, (s).f j = ∑ i, resTop _ (scal (pullback.snd G.hom (jK R)) (c i)) * (b i).f j)) ∧ ∀ s : U.SecK k, ∃! c : Fin (k ^ A.g) → FractionRing R, (∀ j, (s).f j = ∑ i, resTop _ (scal (pullback.snd G.hom (jK R)) (c i)) * (b i).f j) := by
  intro hS R _ _ I D A G _ _ U k hk
  have e₁ : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := congrArg (fun q => q.left) U.gen.inv_hom_id
  have e₂ : U.gen.hom.left ≫ U.gen.inv.left = 𝟙 _ := congrArg (fun q => q.left) U.gen.hom_inv_id
  have H₁ := (hasBasis_field A k hS hk).pull A.isLB (φ' := fun _ => U.gen.hom.left) U.gen.hom.left U.gen.inv.left
    e₁ e₂ (fun _ => Category.comp_id _) _ (pullback.snd G.hom (jK R)) (Over.w U.gen.hom)
  obtain ⟨b, hb⟩ := H₁.of_iso (linComb_isLB _ U.LG.isLB _ _) (linComb_isLB _ A.isLB _ _)
    (iso_pow U.gen.hom.left U.gen.inv.left e₁ e₂ (pullback.fst G.hom (jK R)) U.ext k)
  exact ⟨b, fun c => exists_comb _ b c, hb⟩

end GlobalTheory.GenericSectionBasis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.InducesFrobeniusOnSectionsTranslationIffImageStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
theorem _root_.GlobalTheory.T.inducesFrobeniusOnSections_translation_iff_image : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (N : ℕ), 1 ≤ N → ∀ (p : QkPt D.toPre F N) (x : TFK (R := R) F ⟶ A.A), IndAt U.toUnifPre F N p (translT A.A x) ↔ QkToAkU U.toUnifPre F N p x := by
  first | exact @GlobalTheory.UT.indAt_translT_iff | exact GlobalTheory.UT.indAt_translT_iff | (intros; apply GlobalTheory.UT.indAt_translT_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiTendstoZeroStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
theorem _root_.GlobalTheory.T.finite_not_psiIn_maximalIdeal_pow : (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ θ f, U.Theta θ f → (∃ j, (f 0).f j ≠ 0) → PsiRel D (𝟙_ _) f → ∀ n : ℕ, {χ : D.X | ¬ D.PsiIn χ (IsLocalRing.maximalIdeal V ^ n)}.Finite) := by
  first | exact @GlobalTheory.psi_tendsto_zero | exact GlobalTheory.psi_tendsto_zero | (intros; apply GlobalTheory.psi_tendsto_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbeddingStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.qkToAkU_iff_galois_equivariant : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (F' : Type) [Field F'] [IsAlgClosed F'] [Algebra (FractionRing R) F'] (σ : F →ₐ[FractionRing R] F') (k : ℕ), 1 ≤ k → ∀ (p : QkPt D.toPre F k) (p' : QkPt D.toPre F' k) (x : TFK (R := R) F ⟶ A.A) (x' : TFK (R := R) F' ⟶ A.A), QkExt σ.toRingHom p p' → x'.left = spMap σ.toRingHom ≫ x.left → (QkToAkU U.toUnifPre F k p x ↔ QkToAkU U.toUnifPre F' k p' x') := by
  first | exact @GlobalTheory.TorsionExt.qkToAkU_iff_of_qkExt | exact GlobalTheory.TorsionExt.qkToAkU_iff_of_qkExt | (intros; apply GlobalTheory.TorsionExt.qkToAkU_iff_of_qkExt <;> assumption)
end

