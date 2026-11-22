import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartWiden
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0626
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0505
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelProductIndex.Bundle0001
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0002
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FinrankEqZeroIff
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0121
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0629
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0573
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0628
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineOpenChartCompStructureEqSpMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0615
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0619
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConstantPeriodMarkingUniversalCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0630
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0617
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartLocalGroupFiniteIndexAtFurtherPlace
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.FinAtQ

section Abs

variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] {S : Type} [CommRing S] [Algebra S R]

def mulSub (L : Submodule S (n → R)) (g : ℕ) : AddSubgroup L where
  carrier := {y | ∃ z : L, (y : n → R) = g • (z : n → R)}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro a b ⟨z, hz⟩ ⟨w, hw⟩
    exact ⟨z + w, by simp [hz, hw, smul_add]⟩
  neg_mem' := by
    rintro a ⟨z, hz⟩
    exact ⟨-z, by simp [hz]⟩

def actL (L : Submodule S (n → R)) (x : GL n R) (hx : x ∈ stabGL L) : L →+ L where
  toFun y := ⟨(x : Matrix n n R) *ᵥ (y : n → R), (hx y).1 y.2⟩
  map_zero' := by ext1; simp
  map_add' a b := by ext1; simp [Matrix.mulVec_add]

theorem mulSub_le_comap (L : Submodule S (n → R)) (g : ℕ) (x : GL n R) (hx : x ∈ stabGL L) :
    mulSub L g ≤ (mulSub L g).comap (actL L x hx) := by
  rintro y ⟨z, hz⟩
  refine ⟨actL L x hx z, ?_⟩
  simp only [actL, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [hz, Matrix.mulVec_smul]

def actQ (L : Submodule S (n → R)) (g : ℕ) (x : GL n R) (hx : x ∈ stabGL L) :
    (L ⧸ mulSub L g) →+ (L ⧸ mulSub L g) :=
  QuotientAddGroup.map _ _ (actL L x hx) (mulSub_le_comap L g x hx)

theorem actQ_mk (L : Submodule S (n → R)) (g : ℕ) (x : GL n R) (hx : x ∈ stabGL L) (y : L) :
    actQ L g x hx (y : L ⧸ mulSub L g) = ((actL L x hx y : L) : L ⧸ mulSub L g) := rfl

def rho (L : Submodule S (n → R)) (g : ℕ) (W : Subgroup (GL n R)) (hW : W ≤ stabGL L) :
    W →* AddMonoid.End (L ⧸ mulSub L g) where
  toFun x := actQ L g x (hW x.2)
  map_one' := by
    show actQ L g 1 _ = AddMonoidHom.id _
    refine AddMonoidHom.ext fun q => ?_
    induction q using QuotientAddGroup.induction_on with
    | H y =>
      rw [actQ_mk]
      congr 1
      ext1
      simp [actL]
  map_mul' a b := by
    show actQ L g (a * b : W) _ = (actQ L g a (hW a.2)).comp (actQ L g b (hW b.2))
    refine AddMonoidHom.ext fun q => ?_
    induction q using QuotientAddGroup.induction_on with
    | H y =>
      rw [AddMonoidHom.comp_apply, actQ_mk, actQ_mk, actQ_mk]
      congr 1
      ext1
      simp [actL, Matrix.mulVec_mulVec]

theorem finiteIndex_of_trivOn (L : Submodule S (n → R)) (g : ℕ) (hQ : Finite (L ⧸ mulSub L g))
    (H W : Subgroup (GL n R)) (hW : W ≤ stabGL L)
    (hH : ∀ x ∈ W, (∀ y ∈ L, ∃ z ∈ L, (x : Matrix n n R) *ᵥ y - y = g • z) → x ∈ H) :
    (H.subgroupOf W).FiniteIndex := by
  have hE : Finite (AddMonoid.End (L ⧸ mulSub L g)) :=
    Finite.of_injective (fun f : AddMonoid.End (L ⧸ mulSub L g) => (f : (L ⧸ mulSub L g) → (L ⧸ mulSub L g)))
      (fun a b h => AddMonoidHom.ext (congrFun h))
  have hU : Finite (AddMonoid.End (L ⧸ mulSub L g))ˣ := Finite.of_injective _ Units.val_injective
  have h1 : (rho L g W hW).toHomUnits.ker.FiniteIndex := Subgroup.finiteIndex_ker _
  refine Subgroup.finiteIndex_of_le (H := (rho L g W hW).toHomUnits.ker) ?_
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  have hx' : rho L g W hW x = 1 := congrArg Units.val hx
  rw [Subgroup.mem_subgroupOf]
  refine hH x x.2 fun y hy => ?_
  have h2 : actQ L g x (hW x.2) ((⟨y, hy⟩ : L) : L ⧸ mulSub L g) = ((⟨y, hy⟩ : L) : L ⧸ mulSub L g) :=
    DFunLike.congr_fun hx' _
  rw [actQ_mk, QuotientAddGroup.eq] at h2
  obtain ⟨z, hz⟩ := h2
  refine ⟨-(z : n → R), (-z).2, ?_⟩
  have hz' : -(((x : GL n R) : Matrix n n R) *ᵥ y) + y = g • (z : n → R) := by
    simpa [actL] using hz
  rw [smul_neg, ← hz', neg_add, neg_neg, sub_eq_add_neg, add_comm]

end Abs

section Fin

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem finite_quot (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E))
    (hΛ : Module.Finite (𝓞 E) Λ) (g : ℕ) (hg : g ≠ 0) :
    Finite (latS (F := F) (v.adicCompletion F)
      (tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) Λ ⧸
      mulSub (latS (F := F) (v.adicCompletion F)
      (tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) Λ) g) := by
  set L := latS (F := F) (v.adicCompletion F)
      (tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) Λ with hL
  haveI : Module.Finite ℤ Λ := Module.Finite.trans (𝓞 E) Λ
  obtain ⟨k, s, hs⟩ := Module.Finite.exists_fin (R := ℤ) (M := Λ)
  let m : Fin k → Fin n → E := fun i => (s i : Fin n → E)
  have hm : ∀ i, m i ∈ Λ := fun i => (s i).2
  have hgen : ∀ l ∈ Λ, ∃ z : Fin k → ℤ, l = ∑ i, z i • m i := by
    intro l hl
    have h0 : (⟨l, hl⟩ : Λ) ∈ Submodule.span ℤ (Set.range s) := hs ▸ Submodule.mem_top
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 h0
    refine ⟨c, ?_⟩
    have h1 := congrArg Subtype.val hc
    rw [Submodule.coe_sum] at h1
    simpa [m] using h1.symm
  have key := fun y => PI.LPI.plGen F E (v.adicCompletion F) (v.adicCompletionIntegers F).toSubring n k Λ m hm hgen y
  let c : v.adicCompletionIntegers F := (g : v.adicCompletionIntegers F)
  have hcz : CharZero (v.adicCompletion F) :=
    charZero_of_injective_algebraMap (algebraMap F (v.adicCompletion F)).injective
  have hc : c ≠ 0 := by
    intro h0
    have h1 : ((c : v.adicCompletionIntegers F) : v.adicCompletion F) = 0 := by rw [h0]; rfl
    simp [c, hg] at h1
  haveI : Finite (v.adicCompletionIntegers F ⧸ Ideal.span {c}) :=
    Formalism.UG.P.glint_finite_quotient_of_dvr (Formalism.UG.P.glint_finite_residueField v) _
      (by rwa [Ne, Ideal.span_singleton_eq_bot])
  let sec : v.adicCompletionIntegers F ⧸ Ideal.span {c} → v.adicCompletionIntegers F :=
    Function.surjInv Ideal.Quotient.mk_surjective
  have hmemf : ∀ a : Fin k → v.adicCompletionIntegers F ⧸ Ideal.span {c},
      (fun j => ∑ i, m i j ⊗ₜ[F] ((sec (a i) : v.adicCompletionIntegers F) : v.adicCompletion F)) ∈ L :=
    fun a => (key _).2 ⟨fun i => (sec (a i) : v.adicCompletion F), fun i => (sec (a i)).2, rfl⟩
  let f : (Fin k → v.adicCompletionIntegers F ⧸ Ideal.span {c}) → L ⧸ mulSub L g :=
    fun a => ((⟨_, hmemf a⟩ : L) : L ⧸ mulSub L g)
  refine Finite.of_surjective f ?_
  intro q
  induction q using QuotientAddGroup.induction_on with
  | H y =>
  obtain ⟨a, ha, hy⟩ := (key y).1 y.2
  refine ⟨fun i => Ideal.Quotient.mk _ ⟨a i, ha i⟩, ?_⟩
  have hd : ∀ i, ∃ b : v.adicCompletionIntegers F,
      (sec (Ideal.Quotient.mk _ ⟨a i, ha i⟩) : v.adicCompletionIntegers F) = ⟨a i, ha i⟩ + b * c := by
    intro i
    have h := Function.surjInv_eq (f := Ideal.Quotient.mk (Ideal.span {c})) Ideal.Quotient.mk_surjective
      (Ideal.Quotient.mk _ ⟨a i, ha i⟩)
    rw [Ideal.Quotient.eq] at h
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 h
    exact ⟨b, by rw [hb]; ring⟩
  choose b hb using hd
  show ((⟨_, hmemf _⟩ : L) : L ⧸ mulSub L g) = (y : L ⧸ mulSub L g)
  rw [QuotientAddGroup.eq]
  refine ⟨⟨fun j => ∑ i, m i j ⊗ₜ[F] (((-(b i)) : v.adicCompletionIntegers F) : v.adicCompletion F),
    (key _).2 ⟨_, fun i => (-(b i)).2, rfl⟩⟩, ?_⟩
  funext j
  have e1 : ∀ i, ((sec (Ideal.Quotient.mk _ ⟨a i, ha i⟩) : v.adicCompletionIntegers F) : v.adicCompletion F) =
      a i + g • (b i : v.adicCompletion F) := by
    intro i
    rw [hb i]
    simp [c, nsmul_eq_mul, mul_comm]
  have hneg : ∀ i, (((-(b i)) : v.adicCompletionIntegers F) : v.adicCompletion F) =
      -((b i : v.adicCompletionIntegers F) : v.adicCompletion F) := fun i => rfl
  rw [Submodule.coe_add, Submodule.coe_neg, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, hy]
  simp only [e1, hneg, TensorProduct.tmul_add, Finset.sum_add_distrib, TensorProduct.tmul_smul,
    TensorProduct.tmul_neg, Finset.sum_neg_distrib, Finset.smul_sum, smul_neg]
  abel

end Fin

section Gen

open Formalism.L2.Herm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem finiteIndex_of_princ (hc : CMData F E) (S : HSpace E) (v : HeightOneSpectrum (𝓞 F))
    (Λ : Submodule (𝓞 E) (Fin S.rank → E)) (hΛ : Module.Finite (𝓞 E) Λ) (N : ℕ) (hN : 0 < N)
    (H W : Subgroup (GL (Fin S.rank) (E ⊗[F] v.adicCompletion F)))
    (hW : W ≤ levelVL hc.sig S.gram v Λ) (hH : ∀ x, InPrinc hc S v N Λ x → x ∈ H) :
    (H.subgroupOf W).FiniteIndex := by
  refine finiteIndex_of_trivOn _ N (finite_quot v Λ hΛ N hN.ne') H W (hW.trans inf_le_right) ?_
  intro x hx htriv
  apply hH
  refine ⟨hW hx, ?_⟩
  intro y hy
  obtain ⟨z, hz, e⟩ := htriv y hy
  exact ⟨z, hz, by rw [e, Nat.cast_smul_eq_nsmul]⟩

end Gen

set_option maxHeartbeats 1600000 in

theorem chartLoc_finiteIndex : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Ch0 : B.Word → ℕ → Type) (chOf0 : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch0 u i) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch0 u) (chOf0 u)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (h1 : 1 ≤ B.R.m - 1) (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a (B.R.m - 1)).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) (B.R.m - 1) (Nat.sub_le _ _) (fun c : {c // chOf c = β} => (I.chain l u a).stab (B.R.m - 1) c.1) (fun c => latCrd (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _) (I.latAt u a (B.R.m - 1) c.1))) (g : Ch → Ch0 u (B.R.m - 1)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ u, I.StdF l Z u (F u)) → (∀ u j v h, (F u).glevJ.fr j v h = 1) → (∃ k : Ch → GA B (B.R.N (B.R.m - 1)), I.Reads u a (B.R.m - 1) chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi) (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1) k ∧ ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), I.UnderQ a v → bc (prV (E := B.host.E) v) (k β) = 1) → (∀ β, ∀ v, v ∉ Q → (K β).lev.Uloc v = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.Uloc v) → (∀ β (κ : (K β).lev.U) (κ' : ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.U), κ.1 = κ'.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.chi κ') → ∀ (Lb0 : Submodule (𝓞 (I.rec7 l Z).host.E) (Fin ((I.rec7 l Z).sp.X (B.R.m - 1)).rank → (I.rec7 l Z).host.E)), (F u).levJ.Lb = reL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) Lb0 → ∀ β v, v ∈ Q → ((((K β).lev.Uloc v).comap (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom).subgroupOf (⨆ β', ((K β').lev.Uloc v).comap (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom)).FiniteIndex := by
  intro B X I hOk hPins l Z Ch0 chOf0 F u a Q h1 Ch hCh chOf K g hQ hStd hfr hRd hUl hchi Lb0 hLb β v hv
  have hle := GlobalTheory.T.chart_localGroup_le_baseLattice_level I hOk hPins l Z Ch0 chOf0 F u a Q h1 Ch hCh chOf K g hQ hStd hfr hRd hUl hchi Lb0 hLb
  obtain ⟨N, hN, hpr⟩ :=
    GlobalTheory.T.chart_local_group_contains_principal_congruence I hOk hPins l Z Ch0 chOf0 F u a Q h1 Ch hCh chOf K g hQ hStd hfr hRd hUl hchi Lb0 hLb β v hv
  have hfin : Module.Finite (𝓞 (I.rec7 l Z).host.E) Lb0 := by
    have h0 := (F u).levJ.Lb_fin
    rw [hLb] at h0
    unfold reL at h0
    refine (Module.Finite.equiv_iff (Submodule.equivMapOfInjective
      ((reV (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) (I.rec7 l Z).host.E).toLinearMap.restrictScalars
        (𝓞 (I.rec7 l Z).host.E))
      (reV (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) (I.rec7 l Z).host.E).injective Lb0)).mpr ?_
    exact h0
  exact finiteIndex_of_princ _ _ v Lb0 hfin N hN _ _ (iSup_le fun β' => hle β' v hv) hpr

end GlobalTheory.Mem.Col2.FinAtQ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartTowerHolds
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam
open Formalism.MainNotions.DIV.Cons (SCF intO)
open GlobalTheory.LocM GlobalTheory.LocM.Cht GlobalTheory.Ex GlobalTheory.FullPoint MonObj
open scoped CategoryTheory.Obj

namespace GlobalTheory.LocM.Tower

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {D : Datum H}

theorem nsmul_pow {A Q : Type} [AddCommGroup A] [Group Q] (f : A → Q) (hf : ∀ a c, f (a + c) = f a * f c) (n : ℕ)
    (a : A) : f (n • a) = f a ^ n := by
  induction n with
  | zero =>
    have h := hf 0 0
    rw [add_zero] at h
    rw [zero_smul, pow_zero]
    exact left_eq_mul.1 h
  | succ n ih => rw [succ_nsmul, hf, ih, pow_succ]

theorem ev_eq_of_dvd {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}
    (I : TateIso D k Q act e) {n m : ℕ} (h : n ∣ m) (hm : 0 < m) (a : D.La) : I.ev n a = I.ev m ((m / n) • a) := by
  obtain ⟨j, rfl⟩ := h
  have hn : 0 < n := Nat.pos_of_mul_pos_right hm
  rw [Nat.mul_div_cancel_left _ hn, nsmul_pow _ (I.add _), I.tower n j hn (Nat.pos_of_mul_pos_left hm)]

theorem isFibre_lower {l l' : Geo.Tor.Level H} {B B' : Type} [CommRing B] [CommRing B'] {b : Base l B} {b' : Base l' B'}
    {S S' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'} {ob : Obj D l b s} {ob' : Obj D l' b' s'} (hl : l.Dvd l')
    {r : S' ⟶ S} (ν : SABMap ob'.t ob.t r)
    (h₁ : ∀ a, (ob'.eta a ^ (l'.M / l.M)).left ≫ ν.φ = r ≫ (ob.eta a).left)
    (h₂ : ∀ a, (ob'.etaA a ^ (l'.A / l.A)).left ≫ ν.φ = r ≫ (ob.etaA a).left)
    {K : Type} [Field K] {y : Sp K ⟶ S'} {o : Full D K} (h : IsFibre ob' y o) : IsFibre ob (y ≫ r) o := by
  obtain ⟨φ, g₁, g₂, g₃, g₄, g₅⟩ := h
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  have hM' : 0 < l'.M := lt_of_lt_of_le (by norm_num) l'.three_le
  obtain ⟨w, hw, -⟩ := ν.lin
  refine ⟨φ ≫ ν.φ, g₁.comp ν.cart, LBIso.trans o.P.isLB (pull_isLB ob'.t.PP.isLB _) (pull_isLB ob.t.PP.isLB _) g₂
    (LBIso.chartPull (Geo.Tor.chartPullPull _ _ _ rfl)
      (chartPullSame ob.t.PP.L (fun _ : PUnit => φ ≫ ν.φ) (fun _ => ν.φ) (fun _ => 1) φ fun _ => rfl) ⟨w, hw⟩),
    fun x => ?_, fun v => ?_, fun v hv => ?_⟩
  · rw [← Category.assoc, g₃, Category.assoc, ν.act, Category.assoc]
  · rw [ev_eq_of_dvd o.I hl.2.2 l'.A_pos]
    refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ ν.φ) (g₄ _))).trans ?_
    rw [nsmul_pow _ ob'.etaA_add]
    exact (Category.assoc _ _ _).trans ((congrArg (y ≫ ·) (h₂ v)).trans (Category.assoc _ _ _).symm)
  · obtain ⟨f, hf, e, he, hfe⟩ : ∃ f ∈ l'.Mb, ∃ e ∈ l'.Mb.map (H.bar : 𝓞 E →+* 𝓞 E), f + e = 1 :=
      Submodule.mem_sup.1 (by rw [l'.coprime]; trivial)
    obtain ⟨c, hc⟩ := exists_eq_nsmul l l.prod (hl.2.1 hf) hv
    have e1 : v = e • v + l.M • c := by rw [← hc, ← add_smul, add_comm, hfe, one_smul]
    have e2 : o.I.ev l.M v = o.I.ev l.M (e • v) := by
      conv_lhs => rw [e1]
      rw [o.I.add, (o.I.ker _ hM _).2 ⟨c, rfl⟩, _root_.mul_one]
    rw [e2, ev_eq_of_dvd o.I hl.1 hM',
      ← eta_smul ob (e := e) (by rw [← hfe, add_sub_cancel_right]; exact hl.2.1 hf) v]
    refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ ν.φ)
      (g₅ _ (nsmul_mem (Submodule.smul_mem_smul he Submodule.mem_top) _)))).trans ?_
    rw [nsmul_pow _ ob'.eta_add]
    exact (Category.assoc _ _ _).trans ((congrArg (y ≫ ·) (h₁ _)).trans (Category.assoc _ _ _).symm)

theorem isFractionRing_ball (C : Type) [NormedField C] [IsUltrametricDist C] : IsFractionRing (intO C) C := by
  refine IsFractionRing.of_field _ _ fun z => ?_
  rcases le_total ‖z‖ 1 with h | h
  · exact ⟨⟨z, h⟩, 1, by rw [map_one, div_one]; rfl⟩
  · exact ⟨1, ⟨z⁻¹, by change ‖z⁻¹‖ ≤ 1; rw [norm_inv]; exact inv_le_one_of_one_le₀ h⟩,
      by rw [map_one, one_div]; exact (inv_inv z).symm⟩

section Model

variable {l : Geo.Tor.Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem j_s (Y : Model Xo c β) : Y.j ≫ Y.s = pullback.snd _ _ ≫ spMap β := by
  rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over]

theorem exists_ptC (Y : Model Xo c β) {p : ℕ} (C : SCF p) (f : c.F →+* ↥C.S) (hf : ∀ x, ‖f (β x)‖ ≤ 1)
    (y : Sp ↥C.S ⟶ Xo.XF c) (hy : y ≫ pullback.snd _ _ = spMap f) : ∃ P : PointsOfFlagModel.PtC Y C, P.fK = f ∧ P.y = y := by
  have := projProper _ _ _ Y.proj
  have := isFractionRing_ball ↥C.S
  let alg : O →+* intO ↥C.S := (f.comp β).codRestrict _ hf
  have hE : ValuativeCriterion.Existence Y.s :=
    (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed Y.s) :
      (ValuativeCriterion.Existence ⊓ @QuasiCompact) Y.s).1
  obtain ⟨⟨t⟩⟩ := hE { R := ↥(intO ↥C.S), K := ↥C.S, i₁ := y ≫ Y.j, i₂ := spMap alg, commSq := ⟨by
    rw [Category.assoc, j_s, ← Category.assoc, hy, ← spMap_comp]
    exact spMap_comp alg (intO ↥C.S).subtype⟩ }
  exact ⟨⟨alg, f, rfl, y, hy, t.l, t.fac_right, t.fac_left⟩, rfl, rfl⟩

end Model

variable {Xo : ∀ l : Geo.Tor.Level H, Moduli D l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W}

theorem ptC_ext {i : Idx H p} {C : SCF p} {P P' : PointsOfFlagModel.PtC (Y i) C} (h₁ : P.fK = P'.fK) (h₂ : P.y = P'.y) : P = P' := by
  have h₃ : P.yt = P'.yt := base_ext i _ _ (by rw [P.ext, P'.ext, h₂])
  have h₄ : P.alg = P'.alg := RingHom.ext fun x => Subtype.ext
    ((DFunLike.congr_fun P.compat x).trans (by rw [h₁]; exact (DFunLike.congr_fun P'.compat x).symm))
  cases P; cases P'
  simp only at h₁ h₂ h₃ h₄
  subst h₁ h₂ h₃ h₄
  rfl

theorem sec_cancel {S S' X : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {T : SAB H X} {r : S' ⟶ S} {j : S ⟶ X}
    (ν : SABMap t' t r) (m : SABMap t T j) (σ' : MonoidalCategory.tensorUnit _ ⟶ t'.G)
    (σ : MonoidalCategory.tensorUnit _ ⟶ t.G) (e : σ'.left ≫ ν.φ ≫ m.φ = r ≫ σ.left ≫ m.φ) :
    σ'.left ≫ ν.φ = r ≫ σ.left := by
  apply m.cart.1.hom_ext
  · exact (Category.assoc _ _ _).trans (e.trans (Category.assoc _ _ _).symm)
  · have a₁ : σ'.left ≫ t'.G.hom = 𝟙 _ := Over.w σ'
    have a₂ : σ.left ≫ t.G.hom = 𝟙 _ := Over.w σ
    refine (Category.assoc _ _ _).trans ((congrArg (σ'.left ≫ ·) ν.cart.1.w).trans ?_)
    refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ r) a₁)).trans ?_
    refine Eq.trans ?_ ((Category.assoc _ _ _).trans (congrArg (r ≫ ·) a₂)).symm
    exact (Category.id_comp _).trans (Category.comp_id _).symm

theorem exists_sab_square {S S' X X' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {T : SAB H X} {T' : SAB H X'}
    {r : S' ⟶ S} {j : S ⟶ X} {j' : S' ⟶ X'} {τ : X' ⟶ X} (e : j' ≫ τ = r ≫ j) (m : SABMap t T j)
    (m' : SABMap t' T' j') (mu : SABMap T' T τ) : ∃ ν : SABMap t' t r, m'.φ ≫ mu.φ = ν.φ ≫ m.φ := by
  have h := ObjMaps.exists_sab_comp mu m'
  rw [e] at h
  obtain ⟨n, hn⟩ := h
  obtain ⟨ν, hν⟩ := ObjMaps.exists_sab_cancel m n
  exact ⟨ν, hn.symm.trans hν⟩

theorem ringHom_ext_val {F K : Type} [Field F] [Field K] (V : ValuationSubring F) {f g : F →+* K}
    (h : ∀ x : V, f x = g x) : f = g := by
  ext x
  rcases V.mem_or_inv_mem x with hx | hx
  · exact h ⟨x, hx⟩
  · simpa using h ⟨_, hx⟩

theorem base_square {S S' X X' F F' O O' T : Scheme.{0}} {j : S ⟶ X} {j' : S' ⟶ X'} {s : X ⟶ O} {s' : X' ⟶ O'}
    {q : S ⟶ F} {q' : S' ⟶ F'} {β : F ⟶ O} {β' : F' ⟶ O'} {b : O' ⟶ O} {τ : X' ⟶ X} {r : S' ⟶ S}
    {π' : X' ⟶ pullback s b} (h : j ≫ s = q ≫ β) (h' : j' ≫ s' = q' ≫ β') (e₁ : π' ≫ pullback.fst _ _ = τ)
    (e₂ : π' ≫ pullback.snd _ _ = s') (e₃ : j' ≫ τ = r ≫ j) (y : T ⟶ S') :
    ((y ≫ r) ≫ q) ≫ β = ((y ≫ q') ≫ β') ≫ b := by
  simp only [Category.assoc]
  rw [← h, ← reassoc_of% e₃, ← e₁, Category.assoc, pullback.condition, reassoc_of% e₂, reassoc_of% h']

theorem exists_lower {i i' : Idx H p} {τ : (Y i').X ⟶ (Y i).X} {mu : SABMap (Y i').t (Y i).t τ} (hl : i.l.Dvd i'.l)
    (h : IsTrans i i' τ mu) {K : Type} [Field K] (f : i.c.F →+* K) (f' : i'.c.F →+* K)
    (hf : ∀ (x : i.c.F) (x' : i'.c.F), (x' : ℂ) = x → f' x' = f x) {y' : Sp K ⟶ (Xo i'.l).XF i'.c}
    (hy : y' ≫ pullback.snd _ _ = spMap f') {o : Full D K} (ho : IsFibre (Y i').oF y' o) :
    ∃ y : Sp K ⟶ (Xo i.l).XF i.c, (y ≫ pullback.snd _ _ = spMap f ∧ IsFibre (Y i).oF y o) ∧
      y' ≫ (Y i').j ≫ τ = y ≫ (Y i).j := by
  obtain ⟨b, π', r, hb, e₁, e₂, -, e₃, h₁, h₂⟩ := h
  obtain ⟨ν, hν⟩ := exists_sab_square e₃ (Y i).m (Y i').m mu
  refine ⟨y' ≫ r, ⟨?_, isFibre_lower hl ν
    (fun a => sec_cancel ν (Y i).m _ _ ((congrArg (_ ≫ ·) hν.symm).trans (h₁ a)))
    (fun a => sec_cancel ν (Y i).m _ _ ((congrArg (_ ≫ ·) hν.symm).trans (h₂ a))) ho⟩,
    (congrArg (y' ≫ ·) e₃).trans (Category.assoc _ _ _).symm⟩
  obtain ⟨g, hg⟩ : ∃ g : i.c.F →+* K, (y' ≫ r) ≫ pullback.snd _ _ = spMap g :=
    ⟨(Spec.preimage ((y' ≫ r) ≫ pullback.snd _ _)).hom, (Spec.map_preimage _).symm⟩
  have e₄ : spMap (g.comp (i.c.V W).subtype) = spMap ((f'.comp (i'.c.V W).subtype).comp b) := by
    rw [spMap_comp, spMap_comp, spMap_comp, ← hg, ← hy]
    exact base_square (j_s (Y i)) (j_s (Y i')) e₁ e₂ e₃ y'
  exact hg.trans (congrArg spMap (ringHom_ext_val (i.c.V W) fun x =>
    (DFunLike.congr_fun (spMap_inj e₄) x).trans (hf _ _ (hb x))))

theorem tower : TowerSt := by
  intro E _ _ _ H D Xo p W Y hp hW hpq C i₁ P₁
  have laws : Out.Laws := GlobalTheory.abelianSchemeLaws_all.1
  obtain ⟨j₀, hj, hj'⟩ := GlobalTheory.T.chart_embedding_holds p W i₁.c.F C P₁.fK hp hW i₁.c.fin fun x hx =>
    (DFunLike.congr_fun P₁.compat ⟨x, hx⟩ ▸ (P₁.alg ⟨x, hx⟩).2 : ‖(P₁.fK.comp (i₁.c.V W).subtype) ⟨x, hx⟩‖ ≤ 1)
  have halg : ∀ (i : Idx H p) (x : i.c.F), (x : ℂ) ∈ algebraicClosure ℚ ℂ := fun i x => by
    have := i.c.fin
    exact mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom i.c.F.val)
  let f : ∀ i : Idx H p, i.c.F →+* ↥C.S := fun i =>
    j₀.comp ((i.c.F.val : i.c.F →+* ℂ).codRestrict (algebraicClosure ℚ ℂ) (halg i))
  have hf : ∀ i x, f i x = j₀ ⟨x, halg i x⟩ := fun _ _ => rfl
  have hf₁ : f i₁ = P₁.fK := RingHom.ext fun x => hj x _
  have hz : ∀ n, zeta n ∈ algebraicClosure ℚ ℂ := fun n => by
    rcases n.eq_zero_or_pos with rfl | hn
    · simpa [zeta] using one_mem _
    · exact mem_algebraicClosure_iff.2
        ((Complex.isPrimitiveRoot_exp n hn.ne').isIntegral hn).tower_top.isAlgebraic
  let z₀ : ℕ → (algebraicClosure ℚ ℂ)ˣ := fun n =>
    Units.mk0 ⟨zeta n, hz n⟩ fun h => Complex.exp_ne_zero _ (congrArg Subtype.val h)
  let u : (algebraicClosure ℚ ℂ)ˣ →* ℂˣ := Units.map (algebraicClosure ℚ ℂ).val.toRingHom.toMonoidHom
  have hu : Function.Injective u := Units.map_injective Subtype.val_injective
  have hu₀ : ∀ n, u (z₀ n) = ValInh.zetaU n := fun n => Units.ext rfl
  let z : ℕ → (↥C.S)ˣ := fun n => Units.map j₀.toMonoidHom (z₀ n)
  obtain ⟨o, ho, hc⟩ := exists_isFibre (Y i₁).oF P₁.y
  obtain ⟨hρ, hζ⟩ := hc (P₁.fK.comp (IntermediateField.inclusion i₁.c.le).toRingHom) (by
    rw [pullback.condition, ← Category.assoc, P₁.y_over, spMap_comp])
  obtain ⟨I, hI, hA, hM⟩ := GlobalTheory.T.chart_roots_holds E H D i₁.l _ _ _ _ o.I z hpq
    (fun n hn => (IsPrimitiveRoot.of_map_of_injective (f := u) (hu₀ n ▸ ValInh.zetaU_prim n hn) hu).map_of_injective
      (Units.map_injective j₀.injective))
    (fun n m hn hm => by
      rw [← map_pow]
      exact congrArg _ (hu (by rw [map_pow, hu₀, hu₀, ValInh.zetaU_pow n m hn hm])))
    (Units.ext (Eq.trans (by rw [← hf₁]; rfl) hζ.symm))
  let o' : Full D ↥C.S := { o with I := I }
  have ho' : IsFibre (Y i₁).oF P₁.y o' := by
    obtain ⟨φ, g₁, g₂, g₃, g₄, g₅⟩ := ho
    exact ⟨φ, g₁, g₂, g₃, fun v => (congrArg (fun q => q.left ≫ φ) (hA v)).trans (g₄ v),
      fun v hv => (congrArg (fun q => q.left ≫ φ) (hM v hv)).trans (g₅ v hv)⟩
  have hpt : ∀ i : Idx H p, ∃! y : Sp ↥C.S ⟶ (Xo i.l).XF i.c,
      y ≫ pullback.snd _ _ = spMap (f i) ∧ IsFibre (Y i).oF y o' := fun i =>
    existsUnique_point laws (Y i) (f i) o'
      (fun r hr => hρ.trans (by rw [← hf₁]; exact congrArg j₀ (Subtype.ext hr.symm)))
      (fun r hr => (congrArg Units.val (hI _ i.l.A_pos)).trans (congrArg j₀ (Subtype.ext hr.symm)))
  choose y hy hy' using hpt
  choose P hP hP' using fun i => exists_ptC (Y i) C (f i) (fun x => hj' _ x.2) (y i) (hy i).1
  refine ⟨P, ptC_ext ((hP i₁).trans hf₁) ((hP' i₁).trans (hy' i₁ _ ⟨hf₁ ▸ P₁.y_over, ho'⟩).symm),
    fun i i' τ mu hl h => base_ext i _ _ ?_⟩
  obtain ⟨w, hw, hw'⟩ := exists_lower hl h (f i) (f i') (fun x x' e => congrArg j₀ (Subtype.ext e)) (hy i').1 (hy i').2
  rw [← Category.assoc, (P i').ext, (P i).ext, hP', hP', Category.assoc, hw', hy' i w hw]

end GlobalTheory.LocM.Tower
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenFrameBasePointLiftsUniqueFlagSpaceStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenFrameBasePoint_lifts_unique_flagSpace : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (B : GlobalTheory.ProjVar.Var F) (j : B.X ⟶ gen Z) (f₀ : EigFrame Z (constF e B) (genericPt B ≫ j ≫ genι Z)) (S : Fr (ratOf B) Dw.mult 0) (A₀ : Mat Dw.mult B.Fn) (S' : Fr (ratOf C.Y) Dw.mult Dw.mult) (A₁ : Mat Dw.mult C.Y.Fn) (φ : B.Fn →ₐ[F] C.Y.Fn) (f : C.Y.X ⟶ B.X), j ≫ genStr Z ≫ spMap e.toRingHom = B.str → C.π = f ≫ j → Tied e B j f₀ S A₀ → Tied e C.Y C.π C.f0 S' A₁ → f₀.Coord (φ : B.Fn →+* C.Y.Fn) C.f0 (A₁ * (A₀.map φ)⁻¹) → Refines S S' φ f → ∀ (K : Type) [Field K] (χ : c.F →+* K) (x : Sp K ⟶ gen Z) (x' : Sp K ⟶ B.X), x' ≫ j = x → x ≫ genStr Z = spMap χ → ∀ g : EigFrame Z χ (x ≫ genι Z), ∃! p : Sp K ⟶ C.Y.X, p ≫ f = x' ∧ C.Carries p g := by
  first | exact @GlobalTheory.ShFam.flagex_lifts | exact GlobalTheory.ShFam.flagex_lifts | (intros; apply GlobalTheory.ShFam.flagex_lifts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdaptedEmbeddingStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp tanPull initSpan mem_initSpan)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adapted_embedding : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : ValuationSubring c.F) [IsDiscreteValuationRing V] (M : Model Xo c V.subtype) (X : Scheme.{0}) (π : X ⟶ M.X) (ty : (E →+* ℂ) → Finset ℕ) (A : Atlas M π ty) (σ : E →+* ℂ) (k : ℕ), Geo M π → Nonempty (Adapted A σ k) → ∃ (D : Adapted A σ k) (N : ℕ), Nonempty (D.C.Emb N) := by
  first | exact @GlobalTheory.DRFlag.exists_adapted_emb | exact GlobalTheory.DRFlag.exists_adapted_emb | (intros; apply GlobalTheory.DRFlag.exists_adapted_emb <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsClosedImmersionBlowupGeneratingSectionsStatement
section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_closedImmersion_blowup_generatingSections : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (J : X.IdealSheafData)
    (b : X' ⟶ X) (L₀ : LB X) (m : ℕ) (σ : Fin (m + 1) → L₀.Sec), IsProjOver s → FinalTheorems.Blowup b J →
    GlobalTheory.ProjBlowup.Generates J σ → ∃ (c : X' ⟶ PSpace R m) (hc : b ≫ s = c ≫ PSpace.str R m),
      GlobalTheory.ProjBlowup.Proportional σ b c ∧ IsClosedImmersion (pullback.lift b c hc) := by
  first | exact @GlobalTheory.ProjBlowup.exists_closedImmersion_of_generates | exact GlobalTheory.ProjBlowup.exists_closedImmersion_of_generates | (intros; apply GlobalTheory.ProjBlowup.exists_closedImmersion_of_generates <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConstantLieBasisAnalyticBasisArcStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_constant_lieBasis_analytic_basis_arc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (V : ValuationSubring c.F) (Y : Model Xo c V.subtype) (a : ArcIn Dw l V.subtype ℂ (σ.comp V.subtype)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : GlobalTheory.ArcQ.Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu), ∃ (e : Fin g → Out.GtPt a.D₀ (epsR ℂ)) (v : Fin g → (epsR (PowerSeries ℂ) ⟶ W.t.G)) (z : Fin g → Fin g → ℂ), (∀ k, GlobalTheory.ArcQ.LieImg W (e k) (v k) ∧ GlobalTheory.ArcQ.AnVec Ha (e k) (z k)) ∧ IsLieBasis v ∧ (Matrix.of z).det ≠ 0 := by
  first | exact @GlobalTheory.ArcLieFrame.exists_const_frame | exact GlobalTheory.ArcLieFrame.exists_const_frame | (intros; apply GlobalTheory.ArcLieFrame.exists_const_frame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConstantPeriodMarkingUniversalCoverStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_constant_periodMarking_universalCover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Letter Dw) (Fu : Fam Xo c σ e) (n g' r k : ℕ) (ch : OpenPartialHomeomorph (CxPts (genStr Z) σ) (Fin n → ℂ)) (ex : ExpMaps Z σ g') (lam : (Fin n → ℂ) → Fin r → Fin g' → ℂ) (ρ : Fin g' → Fin r → ℂ), IsLogChart k ch ex lam ρ → ∃ (i : Fin Fu.n) (T₀ : (Fu.Di i).La ≃+ (Fin r → ℤ)), ∀ s ∈ logDom n k, ∀ (a : CxFr Z σ) (W : Letter Dw → Fin g' → ℂ), a.1 = ch.symm (logExp k s) → Dirs a (fun w => (ex a.1 w).left) W → ∃ (Q : (Fu.Di i).La →+ (Letter Dw → ℂ)) (gm : (Fu.Di i).La ≃ₗ[𝓞 E] (Fu.Di i).La), Per Fu a i Q ∧ IsIsom (Fu.Di i) gm ∧ ∀ v, ∑ z, Q (gm v) z • W z = ∑ m, T₀ v m • lam s m := by
  first | exact @GlobalTheory.ShFam.Hor.Mark.exists_marking_const | exact GlobalTheory.ShFam.Hor.Mark.exists_marking_const | (intros; apply GlobalTheory.ShFam.Hor.Mark.exists_marking_const <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIdealSheafAwayFromPStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.HTLine
open Formalism.MainNotions.DIV.Cons (intO SCF)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ideal_sheaf_away_from_p : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (p n : ℕ) (U : Fin n → X.Opens) (m : Fin n → ℕ) (A : ∀ j, Fin (m j) → Γ(X, U j)), (∀ j, IsAffineOpen (U j)) → (∀ j, (p : Γ(X, U j)) ∈ (Ideal.span (Set.range (A j))).radical) → ∃ J : X.IdealSheafData, (∀ x ∈ J.support, x ∉ X.basicOpen (p : Γ(X, ⊤))) ∧ ∀ (W W' : Scheme.{0}) (b : W ⟶ X) (ν : W' ⟶ W), ReciprocityTheory.AnForm.R.FinalTheorems.EffCartier (J.comap b) → ∀ (w : W') (j : Fin n), (ν ≫ b) w ∈ U j → ∃ (V : W'.Opens) (hV : V ≤ (ν ≫ b) ⁻¹ᵁ U j), w ∈ V ∧ IsAffineOpen V ∧ ∃ k, ∀ k', ((ν ≫ b).appLE (U j) V hV).hom (A j k) ∣ ((ν ≫ b).appLE (U j) V hV).hom (A j k') := by
  first | exact @GlobalTheory.Principalise.exists_idealSheaf_principalises | exact GlobalTheory.Principalise.exists_idealSheaf_principalises | (intros; apply GlobalTheory.Principalise.exists_idealSheaf_principalises <;> assumption)
end

