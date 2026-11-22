import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0019
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0750
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0810
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0818
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0819
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0775
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelGroupWithCharacterAtTypePlaces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0610
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingHomExtValuationSubring
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0593
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0643
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0669
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0649
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0679
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0662
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0656
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0697
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0666
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0688
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0766
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0048
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0033
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0761
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0749
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0762
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceModelImp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0717
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0763
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0745
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0754

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDefiniteLevelRecharacterised
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK HkIdx)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.LevelRechar

open ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.LevGChar

section Loc
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {R : Type} [CommRing R]
  {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))}

open Classical in

def dU (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (red : v.adicCompletionIntegers (maximalRealSubfield L) →+* R)
    (r : ℕ) (x : Matrix (Fin n) (Fin n) (v.adicCompletion (maximalRealSubfield L))) : Rˣ :=
  if h : IsUnit (red (NX.intLift v (NX.detT r x))) then h.unit else 1

theorem isUnit_red (red : v.adicCompletionIntegers (maximalRealSubfield L) →+* R) (r : ℕ)
    (x : Matrix (Fin n) (Fin n) (v.adicCompletion (maximalRealSubfield L))) (hdx : Valued.v (NX.detT r x) = 1) :
    IsUnit (red (NX.intLift v (NX.detT r x))) := by
  have hix : NX.detT r x ∈ v.adicCompletionIntegers (maximalRealSubfield L) := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hdx]
  have ex : NX.intLift v (NX.detT r x) = ⟨_, hix⟩ := by rw [NX.intLift, dif_pos hix]
  rw [ex]; exact (isUnit_int hdx hix).map red

theorem dU_eq (red : v.adicCompletionIntegers (maximalRealSubfield L) →+* R) (r : ℕ)
    (x : Matrix (Fin n) (Fin n) (v.adicCompletion (maximalRealSubfield L)))
    (h : IsUnit (red (NX.intLift v (NX.detT r x)))) : dU v red r x = h.unit := by
  unfold dU
  rw [dif_pos h]

theorem dU_mul (red : v.adicCompletionIntegers (maximalRealSubfield L) →+* R)
    (hred : ∀ z : v.adicCompletionIntegers (maximalRealSubfield L),
      Valued.v (z : v.adicCompletion (maximalRealSubfield L)) < 1 → red z = 0) (r : ℕ)
    (x y : Matrix (Fin n) (Fin n) (v.adicCompletion (maximalRealSubfield L)))
    (hx : NX.InParah v r x) (hy : NX.InParah v r y)
    (hdx : Valued.v (NX.detT r x) = 1) (hdy : Valued.v (NX.detT r y) = 1) :
    dU v red r (x * y) = dU v red r x * dU v red r y := by
  have hix : NX.detT r x ∈ v.adicCompletionIntegers (maximalRealSubfield L) := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hdx]
  have hiy : NX.detT r y ∈ v.adicCompletionIntegers (maximalRealSubfield L) := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hdy]
  have ex : NX.intLift v (NX.detT r x) = ⟨_, hix⟩ := by rw [NX.intLift, dif_pos hix]
  have ey : NX.intLift v (NX.detT r y) = ⟨_, hiy⟩ := by rw [NX.intLift, dif_pos hiy]
  have hxy : red (NX.intLift v (NX.detT r (x * y))) =
      red (NX.intLift v (NX.detT r x)) * red (NX.intLift v (NX.detT r y)) := by
    rw [ex, ey, ← map_mul]
    exact red_intLift red hred _ (by simpa using i_detT_mul v r x y hx hy)
  have hux := isUnit_red red r x hdx
  have huy := isUnit_red red r y hdy
  have huxy : IsUnit (red (NX.intLift v (NX.detT r (x * y)))) := by rw [hxy]; exact hux.mul huy
  rw [dU_eq red r _ hux, dU_eq red r _ huy, dU_eq red r _ huxy]
  exact Units.ext (by simp [hxy])

theorem dU_one (red : v.adicCompletionIntegers (maximalRealSubfield L) →+* R)
    (hred : ∀ z : v.adicCompletionIntegers (maximalRealSubfield L),
      Valued.v (z : v.adicCompletion (maximalRealSubfield L)) < 1 → red z = 0) (r : ℕ)
    (x : Matrix (Fin n) (Fin n) (v.adicCompletion (maximalRealSubfield L)))
    (hx : ∀ a b, Valued.v (x a b - (1 : Matrix (Fin n) (Fin n) (v.adicCompletion (maximalRealSubfield L))) a b) < 1) :
    dU v red r x = 1 := by
  have hd : red (NX.intLift v (NX.detT r x)) = 1 := by
    rw [red_intLift red hred 1 (by simpa using i_detT_cong v r x hx), map_one]
  have hu : IsUnit (red (NX.intLift v (NX.detT r x))) := by rw [hd]; exact isUnit_one
  rw [dU_eq red r x hu]
  exact Units.ext (by rw [IsUnit.unit_spec, hd]; rfl)

theorem exists_cong {ι : Type} [Fintype ι] (s : ι → SplitPlace L) : ∃ N : ℕ, 0 < N ∧ ∀ κ : GAf L n, NG.Cong L n N κ →
    ∀ t a b, Valued.v (NX.locM (s t) κ a b -
      (1 : Matrix (Fin n) (Fin n) ((s t).v.adicCompletion (maximalRealSubfield L))) a b) < 1 := by
  have hpos : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)), 0 < Ideal.absNorm v.asIdeal := fun v =>
    Nat.pos_of_ne_zero fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
  have hmem : ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (N : ℕ), Ideal.absNorm v.asIdeal ∣ N →
      (N : 𝓞 (maximalRealSubfield L)) ∈ v.asIdeal := fun v N h =>
    Ideal.mem_of_dvd _ (Nat.cast_dvd_cast h) (Ideal.absNorm_mem _)
  refine ⟨∏ t, Ideal.absNorm (s t).v.asIdeal, Finset.prod_pos fun _ _ => hpos _, fun κ hκ t => ?_⟩
  have hd : Ideal.absNorm (s t).v.asIdeal ∣ ∏ t, Ideal.absNorm (s t).v.asIdeal :=
    Finset.dvd_prod_of_mem (fun t => Ideal.absNorm (s t).v.asIdeal) (Finset.mem_univ t)
  exact locM_cong (s t) (hmem _ _ hd) κ hκ

end Loc

theorem mul_ringHom_units_ratio {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (p : B) (a a' : Aˣ) :
    p * f (a' : A) = p * f (a : A) * f ((a' * a⁻¹ : Aˣ) : A) := by
  rw [mul_assoc, ← map_mul, ← Units.val_mul, mul_comm a', mul_inv_cancel_left]

theorem exists_mul_hom {G H : Type} [Group G] [CommGroup H] {J : Subgroup G} (χ : J →* H) (c : G → H)
    (hc : ∀ κ κ' : J, c ((κ * κ' : J) : G) = c κ * c κ') : ∃ χ' : J →* H, ∀ κ : J, χ' κ = χ κ * c κ :=
  ⟨MonoidHom.mk' (fun κ => χ κ * c κ) (fun κ κ' => by rw [hc, map_mul, mul_mul_mul_comm]), fun _ => rfl⟩

theorem gVal_rechar (D : D7) (i : D.ntw.Tw) (k : ℕ) (b : Bool) (kv : Σ k : Fin 2, D.nd.PlG k) (s : SplitPlace D.host.E)
    (red : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) →+* ZMod (D.host.g kv.1))
    (τ τ' : (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ)
    (x : Matrix (Fin D.R.nV) (Fin D.R.nV) (s.v.adicCompletion (maximalRealSubfield D.host.E)))
    (hu : IsUnit (red (NX.intLift s.v (NX.detT D.R.r x)))) :
    NX.gVal D i k b kv s red τ' x = NX.gVal D i k b kv s red τ x *
      NX.toKk D i k (((τ' (dU s.v red D.R.r x) * (τ (dU s.v red D.R.r x))⁻¹ : (FractionRing (D.ntw.O i))ˣ)) :
        FractionRing (D.ntw.O i)) := by
  unfold NX.gVal
  rw [dif_pos hu, dif_pos hu, dU_eq red _ x hu]
  exact mul_ringHom_units_ratio _ _ _ _

theorem exists_rechar : ∀ (D : D7) (i : D.ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host)) (ψ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (e : ℤ) (W₀ : Type) [AddCommGroup W₀] [Module (FractionRing (D.ntw.O i)) W₀] (ρ₀ : Representation (FractionRing (D.ntw.O i)) (ReciprocityTheory.Aut.GQ D.host.E D.R.nV) W₀) (τ τ' : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ) (M : NX.MtVReal D i j b k Q ψ e W₀ ρ₀ τ), ∃ χ' : M.J →* (NX.Kk D i k)ˣ, (∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong D.host.E D.R.nV N κ → ∃ h : κ ∈ M.J, χ' ⟨κ, h⟩ = 1) ∧ NX.HypOutsideF M.J χ' (NX.badV D i Q) ∧ ∀ κ (h : κ ∈ M.J), ((χ' ⟨κ, h⟩ : (NX.Kk D i k)ˣ) : NX.Kk D i k) = (∏ kv : (Σ kk : Fin 2, D.nd.PlG kk), NX.gVal D i k b kv (M.sp (NX.pG D kv)) (M.redG kv) (τ' kv) (NX.locM (M.sp (NX.pG D kv)) κ)) * (∏ P ∈ M.QP, NX.ofOk D i k (NX.tameVal ψ P e (NX.resRep (M.sp P) P (NX.detT D.R.r (NX.locM (M.sp P) κ)))).1) * (∏ P ∈ M.DP, NX.ofO0 D i k (NX.tameVal (D.ntw.delta i) P (if b then e else -e) (NX.resRep (M.sp P) P (NX.detT D.R.r (NX.locM (M.sp P) κ)))).1) := by
  intro D i j b k Q ψ e W₀ _ _ ρ₀ τ τ' M
  classical
  have hred : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk),
      ∀ z : (M.sp (NX.pG D kv)).v.adicCompletionIntegers (maximalRealSubfield D.host.E),
      Valued.v (z : (M.sp (NX.pG D kv)).v.adicCompletion (maximalRealSubfield D.host.E)) < 1 → M.redG kv z = 0 := by
    intro kv z hz
    haveI : Fact (D.host.g kv.1).Prime := ⟨D.host.g_prime kv.1⟩
    exact i_red_zero _ (M.redG kv) z hz
  have hdet : ∀ (s : SplitPlace D.host.E) (κ : GAf D.host.E D.R.nV), κ ∈ Umax D.host.E D.R.nV →
      NX.InParah s.v D.R.r (NX.locM s κ) → Valued.v (NX.detT D.R.r (NX.locM s κ)) = 1 := fun s κ hU hp =>
    i_detT_one _ _ _ (NX.locM s κ⁻¹) (by rw [← locM_mul, mul_inv_cancel, locM_one]) (locM_int s (inv_mem hU)) hp
  obtain ⟨c, hc⟩ : ∃ c : GAf D.host.E D.R.nV → (NX.Kk D i k)ˣ, ∀ κ, c κ =
      ∏ kv : (Σ kk : Fin 2, D.nd.PlG kk), Units.map (NX.toKk D i k).toMonoidHom
        (τ' kv (dU (M.sp (NX.pG D kv)).v (M.redG kv) D.R.r (NX.locM (M.sp (NX.pG D kv)) κ)) *
          (τ kv (dU (M.sp (NX.pG D kv)).v (M.redG kv) D.R.r (NX.locM (M.sp (NX.pG D kv)) κ)))⁻¹) := ⟨_, fun _ => rfl⟩
  have hmul : ∀ κ κ' : M.J, c ((κ * κ' : M.J) : GAf D.host.E D.R.nV) = c κ * c κ' := by
    rintro ⟨κ, hκ⟩ ⟨κ', hκ'⟩
    obtain ⟨h1, h2, -⟩ := (M.J_mem κ).1 hκ
    obtain ⟨h1', h2', -⟩ := (M.J_mem κ').1 hκ'
    show c (κ * κ') = c κ * c κ'
    rw [hc, hc, hc, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun kv _ => ?_
    rw [locM_mul, dU_mul _ (hred kv) _ _ _ (h2 kv).1 (h2' kv).1 (hdet _ _ h1 (h2 kv).1) (hdet _ _ h1' (h2' kv).1),
      ← MonoidHom.map_mul, map_mul (τ kv), map_mul (τ' kv), mul_inv, mul_mul_mul_comm]
  have hone : ∀ κ : GAf D.host.E D.R.nV,
      (∀ kv a b, Valued.v (NX.locM (M.sp (NX.pG D kv)) κ a b - (1 : Matrix (Fin D.R.nV) (Fin D.R.nV)
        ((M.sp (NX.pG D kv)).v.adicCompletion (maximalRealSubfield D.host.E))) a b) < 1) → c κ = 1 := by
    intro κ hg
    rw [hc]
    refine Finset.prod_eq_one fun kv _ => ?_
    rw [dU_one _ (hred kv) _ _ (hg kv), map_one, map_one, inv_one, mul_one, map_one]
  obtain ⟨χ', hχ'⟩ := exists_mul_hom M.χ c hmul
  have hχ : ∀ κ (h : κ ∈ M.J), χ' ⟨κ, h⟩ = M.χ ⟨κ, h⟩ * c κ := fun κ h => hχ' ⟨κ, h⟩
  refine ⟨χ', ?_, ?_, ?_⟩
  · obtain ⟨N, hN, hJ⟩ := M.J_open
    obtain ⟨N', hN', hc'⟩ := exists_cong (n := D.R.nV)
      (fun kv : (Σ kk : Fin 2, D.nd.PlG kk) => M.sp (NX.pG D kv))
    refine ⟨N * N', Nat.mul_pos hN hN', fun κ hκ => ?_⟩
    obtain ⟨h, h1⟩ := hJ κ hκ.of_mul_left
    refine ⟨h, ?_⟩
    have h2 : c κ = 1 := hone κ (hc' κ hκ.of_mul_right)
    rw [hχ, h1, h2, one_mul]
  · intro κ hκ
    refine ⟨(M.hyp κ hκ).1, fun h => ?_⟩
    rw [hχ, (M.hyp κ hκ).2 h, one_mul]
    refine hone κ fun kv a b => ?_
    have hw := (M.sp (NX.pG D kv)).w_under
    rw [M.sp_w _ (Or.inr (Or.inr ⟨kv, rfl⟩))] at hw
    have hb : (M.sp (NX.pG D kv)).v ∈ NX.badV D i Q :=
      ⟨NX.pG D kv, hw, Or.inr (Or.inl ⟨kv.1, D.naut.plGw_over kv.1 kv.2⟩)⟩
    rw [locM_triv _ hκ hb]
    simp
  · intro κ h
    obtain ⟨h1, h2, -⟩ := (M.J_mem κ).1 h
    rw [hχ, Units.val_mul, M.chi_eq κ h, hc, Units.coe_prod,
      Finset.prod_congr rfl fun kv _ => gVal_rechar D i k b kv (M.sp (NX.pG D kv)) (M.redG kv) (τ kv) (τ' kv) _
        (isUnit_red _ _ _ (hdet _ _ h1 (h2 kv).1)), Finset.prod_mul_distrib]
    simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
    ring

end GlobalTheory.LevelRechar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFlagClosure
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)

namespace GlobalTheory.GrCl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

theorem exists_gap (s : Finset ℕ) {k m : ℕ} (hk : k ≤ m) : ∃ a b, a ≤ k ∧ k ≤ b ∧ (a ∈ s ∨ a = 0) ∧ (b ∈ s ∨ b = m) ∧
    ∀ e ∈ s, e ≤ a ∨ b ≤ e := by
  classical
  have ex : ∃ b, k ≤ b ∧ (b ∈ s ∨ b = m) := ⟨m, hk, .inr rfl⟩
  refine ⟨Nat.findGreatest (· ∈ s) k, Nat.find ex, Nat.findGreatest_le k, (Nat.find_spec ex).1, ?_, (Nat.find_spec ex).2,
    fun e he => ?_⟩
  · by_cases h : Nat.findGreatest (· ∈ s) k = 0
    · exact .inr h
    · exact .inl (Nat.findGreatest_of_ne_zero rfl h)
  · rcases le_total e k with h | h
    · exact .inl (Nat.le_findGreatest h he)
    · exact .inr (Nat.find_min' ex ⟨h, .inl he⟩)

theorem isMap_refl (Z : Mdl Y i₀) : IsMap Z Z (𝟙 _) := by
  refine ⟨MapComp.corr_refl Z, fun k _ w hw => ?_⟩
  obtain ⟨mu, hmu, ht⟩ := exists_isTrans_id (Y := Y) Z.i
  obtain ⟨a, φ, e⟩ := Z.exists_chart w hw
  have h : Z.FlagAt w ((Z.fr a).bc φ) := (atlasOf Z).flagAt_fr (a := a) e
  refine ⟨𝟙 _, mu, _, ht, by simp, h, ?_⟩
  simpa only [hmu, Category.comp_id] using h

open Classical in

theorem exists_step (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (Z : Mdl Y i₀) (t : Step Y i₀) (ht : ∃ g, IsMap Z t.B g) :
    ∃ Z' : Mdl Y i₀, Z'.i = Z.i ∧ Z'.ty = Function.update Z.ty t.σ (insert t.k (Z.ty t.σ)) ∧ (∃ f, IsMap Z' Z f) ∧
      t.Holds Z' ∧ ∀ Z'' : Mdl Y i₀, (∃ g, IsMap Z'' Z g) → t.Holds Z'' → ∃ h, IsMap Z'' Z' h := by
  have := isDiscreteValuationRing_V Z.i.c W hp hW
  have : CharZero Z.i.c.F := RingHom.charZero Z.i.c.F.val.toRingHom
  obtain ⟨g, hg⟩ := ht
  obtain ⟨D, hD⟩ := GlobalTheory.T.exists_lattice_coordinates_step E H Dw Xo p W Y i₀ hp hW t Z g hg
  obtain ⟨A, hA, α, hα⟩ := GlobalTheory.DRFlag.Atlas.exists_refine E H Dw _ _ _ _ _ _ _ _ (atlasOf Z) D.C
  obtain ⟨cv, Dv, hc, hl, hgl⟩ := GlobalTheory.T.atlas_lattice_coordinates E H Dw _ _ _ _ _ _ _ _ A D t.σ α hα
  obtain ⟨a, b, ha, hb, ha', hb', gap⟩ := exists_gap (Z.ty t.σ) t.le
  have geo := geoOf Z
  obtain ⟨X', f, q, κ, cl⟩ := GlobalTheory.T.cells_of_charts_polynomial _ Z.X (Z.π ≫ (Y Z.i).s) geo.proj geo.normal geo.flat A.ch
    (fun j => (A.alg j).comp (Z.i.c.V W).subtype) (GVar (Dw.mult t.σ) a t.k b) (GPm (Dw.mult t.σ) a b) _
    (fun j => gxi a b t.le (cv j)) (fun j => gell a b t.le (Dv j)) A.alg_s
    (fun j => ⟨fun w => (GlobalTheory.T.cell_coordinate_polynomials_surjective _ _ a _ b _ t.le _ _ w ha hb (hl j)).1,
      fun w => (GlobalTheory.T.cell_coordinate_polynomials_surjective _ _ a _ b _ t.le _ _ w ha hb (hl j)).2,
      fun K _ w w' ψ' h => (GlobalTheory.T.cell_coordinates_base_change K _ _ _ a _ b _ t.le _ _ _ _ (ψ'.comp MvPolynomial.C) ψ' w' ha hb (hl j) (hl j)
        fun _ _ => rfl).2 w h,
      GlobalTheory.T.cell_coordinate_linear_relation _ _ a _ b _ t.le _ _ ha hb (hl j)⟩)
    (fun K _ j j' φ w' ψ' e => by
      obtain ⟨⟨w, hw⟩, h⟩ := GlobalTheory.T.cell_coordinates_base_change K _ _ _ a _ b _ t.le _ _ _ _ φ ψ' w' ha hb (hl j) (hl j') fun r hr =>
        hgl K j j' φ _ e r (by rcases hr with rfl | rfl <;> tauto)
      exact ⟨w, h w hw⟩)
  let ty' := Function.update Z.ty t.σ (insert t.k (Z.ty t.σ))
  have t₁ : ty' t.σ = insert t.k (Z.ty t.σ) := Function.update_self _ _ _
  have t₂ : ∀ σ', σ' ≠ t.σ → ty' σ' = Z.ty σ' := fun σ' h => Function.update_of_ne h _ _
  obtain ⟨A', rel⟩ := GlobalTheory.T.cell_atlas_from_lattice E H Dw _ _ _ _ _ _ _ _ A D t.σ α cv Dv a t.k b t.le X' f q κ ty' ha hb ha' hb' gap hα hc hl
    cl t₁ t₂
  have hcar : A'.ch.carrier = f ⁻¹' A.ch.carrier := by
    rw [A'.cover, A.cover, Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp]
  have geo' : Geo (Y Z.i) (f ≫ Z.π) :=
    ⟨by rw [Category.assoc]; exact cl.proj, cl.normal, by rw [Category.assoc]; exact cl.flat,
      A'.cover ▸ hcar ▸ cl.dense⟩
  have up' : ∀ (K : Type) [Field K] (w : Sp K ⟶ X') (u : Vecs Dw (Y Z.i).t K), A'.FlagAt w u →
      ∃ U : TVecs Dw (Y Z.i).t ((w ≫ f) ≫ Z.π), up U = u := fun K _ w u hu => by
    obtain ⟨a, φ, -, hfr, -⟩ := hu
    rw [← Category.assoc] at hfr
    exact exists_up fun σ i => (hfr.1 σ i).1
  have down : ∀ (K : Type) [Field K] (w : Sp K ⟶ X') (u : Vecs Dw (Y Z.i).t K), A'.FlagAt w u →
      (atlasOf Z).FlagAt (w ≫ f) u := fun K _ w u hu => by
    obtain ⟨U, rfl⟩ := up' K w u hu
    exact (hA K _ _).1 ((rel K w U).1 hu).1
  have red : IsReduced X' := by
    have := fun x => (cl.normal x).1
    exact isReduced_of_isReduced_stalk _
  have pl : Planar D.Em f q := GlobalTheory.T.planar_of_dense_carriers _ _ _ _ _ _ D.Em f q A'.ch.carrier red (hcar ▸ cl.dense) fun K _ w hw β h => by
    obtain ⟨j, φ, e⟩ := A'.ch.exists_fac w (hw ⟨_, rfl⟩)
    have hu := A'.flagAt_fr e
    obtain ⟨U, hU⟩ := up' K w _ hu
    exact ⟨_, ((rel K w U).1 (hU ▸ hu)).2 β h⟩
  obtain ⟨Z', e, hi, hty, m₁, m₂, -⟩ := GlobalTheory.T.exists_model_of_atlas E H Dw Xo p W Y i₀ Z.i X' _ ty' A' Z.dvd Z.le geo'
  have sub : ∀ σ, Z.ty σ ⊆ ty' σ := fun σ => by
    by_cases h : σ = t.σ
    · rw [h, t₁]; exact Finset.subset_insert _ _
    · rw [t₂ σ h]
  have hf : IsMap Z' Z (e.hom ≫ f) :=
    ⟨⟨hi ▸ ⟨dvd_rfl, le_rfl, dvd_rfl⟩, hi ▸ le_rfl, hty ▸ sub⟩, m₂ _ _ _ (atlasOf Z) f rfl down⟩
  have he : MapsTo Z' A' e.hom := by
    simpa only [Category.comp_id] using m₂ _ _ _ A' (𝟙 _) (Category.id_comp _) fun K _ w u h => by
      simpa only [Category.comp_id] using h
  refine ⟨Z', hi, hty, ⟨_, hf⟩, GlobalTheory.T.lattice_step_atlas_pullback E H Dw Xo p W Y i₀ hp hW t Z g D hg hD A X' f q ty' A' hA rel pl Z' _ he hf
    (by rw [hty, t₁]; exact Finset.mem_insert_self _ _), fun Z'' ⟨g₀, hg₀⟩ hH => ?_⟩
  have sub' : ∀ σ, ty' σ ⊆ Z''.ty σ := fun σ => by
    by_cases h : σ = t.σ
    · rw [h, t₁]; exact Finset.insert_subset hH.1 (hg₀.1.2.2 _)
    · rw [t₂ σ h]; exact hg₀.1.2.2 _
  obtain ⟨h, hh⟩ := GlobalTheory.T.atlas_model_comparison E H Dw Xo p W Y i₀ Z.i _ _ ty' A' Z'' hp hW geo' hg₀.1.2.1 sub'
    (GlobalTheory.T.lattice_step_atlas_refinement E H Dw Xo p W Y i₀ hp hW t Z g D hg hD A X' f q ty' A' hA rel cl.ovr cl.lift Z'' g₀ hg₀ hH)
  exact ⟨h ≫ e.inv, ⟨hi ▸ hg₀.1.1, hi ▸ hg₀.1.2.1, hty ▸ sub'⟩, m₁ Z'' h hh⟩

theorem exists_isFlagCl : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Y : LocalSystem Xo p W) (i₀ : Idx H p), ∀ (Z : Mdl Y i₀) (s : Finset (Step Y i₀)), (∀ t ∈ s, ∃ f, IsMap Z t.B f) → ∃ Z', IsFlagCl Z s Z' := by
  classical
  intro E _ _ _ H Dw Xo p W hp hW Y i₀ Z s
  induction s using Finset.induction_on with
  | empty => exact fun _ => ⟨Z, isFlagCl_empty ⟨_, isMap_refl Z⟩⟩
  | insert t s _ ih =>
    intro h
    obtain ⟨Z₁, hi, hty, ⟨f, hf⟩, hs, mn⟩ := ih fun t' ht' => h t' (Finset.mem_insert_of_mem ht')
    obtain ⟨g, hg⟩ := h t (Finset.mem_insert_self _ _)
    obtain ⟨Z₂, hi', hty', ⟨f', hf'⟩, ht, mn'⟩ := exists_step hp hW Z₁ t ⟨_, MapComp.isMap_comp hf hg⟩
    refine ⟨Z₂, hi'.trans hi, fun σ => ?_, ⟨_, MapComp.isMap_comp hf' hf⟩, fun t' ht' => ?_, fun Z'' hg' hH => ?_⟩
    · rw [hty']
      ext r
      by_cases e : σ = t.σ
      · subst e
        simp only [Function.update_self, hty, Finset.mem_insert, Finset.mem_union, mem_stepTy, exists_eq_or_imp, true_and]
        tauto
      · simp only [Function.update_of_ne e, hty, Finset.mem_insert, Finset.mem_union, mem_stepTy, exists_eq_or_imp,
          Ne.symm e, false_and, false_or]
    · rcases Finset.mem_insert.1 ht' with rfl | ht'
      · exact ht
      · exact GlobalTheory.T.step_holds_of_map E H Dw Xo p W hp hW Y i₀ t' Z₁ Z₂ ⟨_, hf'⟩ (hs t' ht')
    · exact mn' Z'' (mn Z'' hg' fun t' ht' => hH t' (Finset.mem_insert_of_mem ht')) (hH t (Finset.mem_insert_self _ _))

end GlobalTheory.GrCl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGeoExtN
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000
open GlobalTheory.HeightCounting.SerMove

open GlobalTheory.Mem.R3.Tr GlobalTheory.Mem.R3.Rw.StateChecks

namespace GlobalTheory.HeightCounting.SerMove.ReGeo

variable {B : Base} {f : Top.Fr B.toPre} {T : TwDat B} {w : ColW B f T} {hX : B.fields.Ok} {Wt : Set B.places.Pl}

set_option maxHeartbeats 4000000 in

theorem geo_copy {Z Z' : w.Lt} (z₀ : Dat (w.st Z) w.I hX T Wt) (z : Dat (w.st Z') w.I hX T Wt) (h1 : z.Xg = z₀.Xg)
    (h2 : z.tr = z₀.tr) (h3 : HEq z.core (coreJ (a := Z) Z' z₀.core)) (h4 : HEq z.R (real3 (a := Z) Z' (iK := z₀.alg) z₀.R))
    (hg : GlobalTheory.RealGeo.InGeo z₀.geo) :
    ∃ g : GlobalTheory.RealGeo.GeoHalf z.core z.R.toRealDat (fun _ => 1), GlobalTheory.RealGeo.InGeo g ∧
      (∀ {B' : Base} {f' : Top.Fr B'.toPre} {T' : TwDat B'} {w' : ColW B' f' T'} {Z'' : w'.Lt} {hX' : B'.fields.Ok}
        {Wt' : Set B'.places.Pl} (z' : Dat (w'.st Z'') w'.I hX' T' Wt'), ExtN z₀ z' → ExtN { z with geo := g } z') ∧
      (∀ {B' : Base} {f' : Top.Fr B'.toPre} {T' : TwDat B'} {w' : ColW B' f' T'} {Z'' : w'.Lt} {hX' : B'.fields.Ok}
        {Wt' : Set B'.places.Pl} (z' : Dat (w'.st Z'') w'.I hX' T' Wt'), ExtN z' z₀ → ExtN z' { z with geo := g }) := by
  obtain @⟨Xg, tr, core, al, alg_eq, R, cG, geo, pins, lev, idG, good, mu, l1, l2⟩ := z
  dsimp only at h1 h2 h3 h4 ⊢
  subst h1 h2
  obtain rfl : core = coreJ (a := Z) Z' z₀.core := eq_of_heq h3
  have e : al = (by with_unfolding_all exact ((alg (a := Z) Z' z₀.alg) :)) := by
    refine Algebra.algebra_ext _ _ fun y => B.embLL.injective ?_
    exact (alg_eq y).trans ((by with_unfolding_all exact ((z₀.alg_eq ((by with_unfolding_all exact (y :)))).symm :)))
  subst e
  obtain rfl : R = cpR (a := Z) Z' z₀ := eq_of_heq (h4.trans ((by with_unfolding_all exact ((HEq.refl (cpR (a := Z) Z' z₀)) :))))
  refine ⟨(by with_unfolding_all exact ((geoHalf (a := Z) Z' (iK := z₀.alg) z₀.geo) :)), (by with_unfolding_all exact ((inGeo_tr (a := Z) Z' (iK := z₀.alg) hg) :)), ?_, ?_⟩
  · intro B' f' T' w' Z'' hX' Wt' z' e
    exact
      { H := (by with_unfolding_all exact (e.H :))
        l := (by with_unfolding_all exact (e.l :))
        c := (by with_unfolding_all exact (e.c :))
        Dw := (by with_unfolding_all exact (e.Dw :))
        Xo := (by with_unfolding_all exact (e.Xo :))
        U := (by with_unfolding_all exact (e.U :))
        V := (by with_unfolding_all exact (e.V :))
        dict := (by with_unfolding_all exact (e.dict :))
        mu := (by with_unfolding_all exact (e.mu :))
        Kf := (by with_unfolding_all exact (e.Kf :))
        cE := (by with_unfolding_all exact (e.cE :))
        chiW := (by with_unfolding_all exact (e.chiW :))
        x₀ := (by with_unfolding_all exact (e.x₀ :))
        iota := (by with_unfolding_all exact (e.iota :))
        ψ := (by with_unfolding_all exact (e.ψ :))
        θ := (by with_unfolding_all exact (e.θ :))
        βW := (by with_unfolding_all exact (e.βW :))
        βY := (by with_unfolding_all exact (e.βY :))
        nW := (by with_unfolding_all exact (e.nW :))
        βV := (by with_unfolding_all exact (e.βV :))
        ΛV := (by with_unfolding_all exact (e.ΛV :))
        ΛW := (by with_unfolding_all exact (e.ΛW :))
        Pg := (by with_unfolding_all exact (e.Pg :))
        eG := (by with_unfolding_all exact (e.eG :))
        Sb := (by with_unfolding_all exact (e.Sb :))
        BV := (by with_unfolding_all exact (e.BV :))
        MW := (by with_unfolding_all exact (e.MW :))
        forms := (by with_unfolding_all exact (e.forms :))
        cV := (by with_unfolding_all exact (e.cV :))
        pb := (by with_unfolding_all exact (e.pb :))
        ΛY := (by with_unfolding_all exact (e.ΛY :))
        κ := (by with_unfolding_all exact (e.κ :))
        ref := (by with_unfolding_all exact (e.ref :))
        jL := (by with_unfolding_all exact (e.jL :)) }
  · intro B' f' T' w' Z'' hX' Wt' z' e
    exact
      { H := (by with_unfolding_all exact (e.H :))
        l := (by with_unfolding_all exact (e.l :))
        c := (by with_unfolding_all exact (e.c :))
        Dw := (by with_unfolding_all exact (e.Dw :))
        Xo := (by with_unfolding_all exact (e.Xo :))
        U := (by with_unfolding_all exact (e.U :))
        V := (by with_unfolding_all exact (e.V :))
        dict := (by with_unfolding_all exact (e.dict :))
        mu := (by with_unfolding_all exact (e.mu :))
        Kf := (by with_unfolding_all exact (e.Kf :))
        cE := (by with_unfolding_all exact (e.cE :))
        chiW := (by with_unfolding_all exact (e.chiW :))
        x₀ := (by with_unfolding_all exact (e.x₀ :))
        iota := (by with_unfolding_all exact (e.iota :))
        ψ := (by with_unfolding_all exact (e.ψ :))
        θ := (by with_unfolding_all exact (e.θ :))
        βW := (by with_unfolding_all exact (e.βW :))
        βY := (by with_unfolding_all exact (e.βY :))
        nW := (by with_unfolding_all exact (e.nW :))
        βV := (by with_unfolding_all exact (e.βV :))
        ΛV := (by with_unfolding_all exact (e.ΛV :))
        ΛW := (by with_unfolding_all exact (e.ΛW :))
        Pg := (by with_unfolding_all exact (e.Pg :))
        eG := (by with_unfolding_all exact (e.eG :))
        Sb := (by with_unfolding_all exact (e.Sb :))
        BV := (by with_unfolding_all exact (e.BV :))
        MW := (by with_unfolding_all exact (e.MW :))
        forms := (by with_unfolding_all exact (e.forms :))
        cV := (by with_unfolding_all exact (e.cV :))
        pb := (by with_unfolding_all exact (e.pb :))
        ΛY := (by with_unfolding_all exact (e.ΛY :))
        κ := (by with_unfolding_all exact (e.κ :))
        ref := (by with_unfolding_all exact (e.ref :))
        jL := (by with_unfolding_all exact (e.jL :)) }

end GlobalTheory.HeightCounting.SerMove.ReGeo

namespace GlobalTheory.HeightCounting.SerMove

theorem exists_geo_extN : ∀ {K : Ctx} {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'} {P : Pre2 K w} {P' : Pre2 K w'}, Ext P.z P'.z → ∀ (x : St P) (x' : St P'), ∃ (g : Geo x) (g' : Geo x'), GlobalTheory.RealGeo.InGeo g ∧ GlobalTheory.RealGeo.InGeo g' ∧ ExtN (datAt x g) (datAt x' g') := by
  intro K B B' f f' T T' w w' P P' e x x'
  obtain ⟨g, hg, hL, -⟩ := ReGeo.geo_copy (Z := P.Z₀) (Z' := x.o.Z) P.z x.m.z x.m.Xg x.m.tr ((by with_unfolding_all exact (x.copy.core :))) ((by with_unfolding_all exact (x.copy.R :))) P.inGeo
  obtain ⟨g', hg', -, hR⟩ :=
    ReGeo.geo_copy (Z := P'.Z₀) (Z' := x'.o.Z) P'.z x'.m.z x'.m.Xg x'.m.tr ((by with_unfolding_all exact (x'.copy.core :))) ((by with_unfolding_all exact (x'.copy.R :))) P'.inGeo
  exact ⟨g, g', hg, hg', hR _ (hL _ e.extN)⟩

end GlobalTheory.HeightCounting.SerMove
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalUnitCharacterNontrivialStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_unit_character_nontrivial : ∀ (D : D7) (cf : CharFrame D) (j : Fin D.R.m) (ξH : HChar D.host.E) (s : SplitPlace D.host.E) (ξ : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ), ξH.TrivOn D.host.F → (∀ u, ξH.TameAt u) → s.v ∈ qPl D (cf.mu0 j * ξH) → NG.IsCompAt (cf.mu0 j * ξH) s ξ → ∃ a : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ, Valued.v (a : s.v.adicCompletion (maximalRealSubfield D.host.E)) = 1 ∧ ξ a ≠ 1 := by
  first | exact @GlobalTheory.CompRamified.exists_unit_ne_one | exact GlobalTheory.CompRamified.exists_unit_ne_one | (intros; apply GlobalTheory.CompRamified.exists_unit_ne_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMovedDataLaterStagesWithNewTwistStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_movedData_laterStagesWithNewTwist : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (N : TwNew (Dof x)), ∃ m : Moved (oTw x N), m.z = datTw x N ∧ m.Copy ∧ m.Coh := by
  first | exact @GlobalTheory.HeightCounting.Up.MvTw.moved_tw | exact GlobalTheory.HeightCounting.Up.MvTw.moved_tw | (intros; apply GlobalTheory.HeightCounting.Up.MvTw.moved_tw <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSplitReductionStandardFrameConjStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.HeightCounting GlobalTheory.CenFrame
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_split_reduction_standard_frame_conj : ∀ (D : D7) (V : HSp D) (n : ℕ) (hn : V.rank = n) (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V n) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), R3.StdFrame hF P → IsBaseFrame V β Λ 1 → ∀ s : ReciprocityTheory.Aut.SplitPlace D.host.E, ∃ (φ : Os s →+* kP s.w) (b : GL (Fin n) (kP s.w)), IsResidue s φ ∧ FrameRed hn P β s φ b := by
  first | exact @GlobalTheory.FrameRedSplit.frameRed_exists | exact GlobalTheory.FrameRedSplit.frameRed_exists | (intros; apply GlobalTheory.FrameRedSplit.frameRed_exists <;> assumption)
end

