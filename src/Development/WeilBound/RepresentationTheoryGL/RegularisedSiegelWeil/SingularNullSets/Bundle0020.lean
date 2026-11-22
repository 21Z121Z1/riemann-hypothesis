import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle0018
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0040
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0054
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle0019
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0744
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsGoodCompatThree
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0190
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0173
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacobiMapsExist
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0416

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.FixMulKer
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LApproxId

variable {F : Type} [Field F] [NumberField F]

theorem fst_eq (x : AF F) : fstA F x = x.1 := rfl
theorem snd_eq (x : AF F) : sndA F x = x.2 := rfl

theorem idF_fst {S : Finset (HeightOneSpectrum (𝓞 F))} {ε : AF F} (hε : IsIdF S ε) : ε.1 = 1 := hε.1

open Classical in
theorem idF_snd {S : Finset (HeightOneSpectrum (𝓞 F))} {ε : AF F} (hε : IsIdF S ε) (v : HeightOneSpectrum (𝓞 F)) :
    ε.2 v = if v ∈ S then 1 else 0 := hε.2 v

theorem idF_mul {S : Finset (HeightOneSpectrum (𝓞 F))} {ε : AF F} (hε : IsIdF S ε) : ε * ε = ε := by
  classical
  refine Prod.ext ?_ (FiniteAdeleRing.ext _ fun v => ?_)
  · change ε.1 * ε.1 = ε.1
    rw [idF_fst hε, one_mul]
  · change ε.2 v * ε.2 v = ε.2 v
    rw [idF_snd hε v]
    split_ifs <;> simp

theorem ker_fst {S : Finset (HeightOneSpectrum (𝓞 F))} {ε : AF F} (hε : IsIdF S ε) {y : AF F} (hy : ε * y = 0) :
    y.1 = 0 := by
  have h : (ε * y).1 = 0 := by rw [hy]; rfl
  change ε.1 * y.1 = 0 at h
  rwa [idF_fst hε, one_mul] at h

theorem ker_snd {S : Finset (HeightOneSpectrum (𝓞 F))} {ε : AF F} (hε : IsIdF S ε) {y : AF F} (hy : ε * y = 0)
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∈ S) : y.2 v = 0 := by
  classical
  have h : (ε * y).2 v = 0 := by rw [hy]; rfl
  change ε.2 v * y.2 v = 0 at h
  rwa [idF_snd hε v, if_pos hv, one_mul] at h

theorem fix_snd {S : Finset (HeightOneSpectrum (𝓞 F))} {ε : AF F} (hε : IsIdF S ε) {h : AF F} (hh : ε * h = h)
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) : h.2 v = 0 := by
  classical
  have h' : (ε * h).2 v = h.2 v := by rw [hh]
  change ε.2 v * h.2 v = h.2 v at h'
  rw [idF_snd hε v, if_neg hv, zero_mul] at h'
  exact h'.symm

theorem fix_mul_ker {ε h y : AF F} (hε : ε * ε = ε) (hh : ε * h = h) (hy : ε * y = 0) : h * y = 0 := by
  calc h * y = (ε * h) * y := by rw [hh]
    _ = h * (ε * y) := by ring
    _ = 0 := by rw [hy, mul_zero]

end PositivityTheory.Rg.Rsw.L.LApproxId

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LCutId_B
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LCutId

variable {D : D7} {n : ℕ}

theorem omega_fix {W : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χ θ} {μ : Measure (Mx D W.rank n)}
    {ω : G D n →* Module.End ℂ (schwartzA θ W.rank n)} (hω : IsWeilSch ψ χ θ W μ ω)
    {nb : hermA D n → G D n} (hnb : IsNMap nb) {v : Pl D} (Ψ : schwartzA θ W.rank n) (hΨ : ∀ k ∈ KAt D n v, ω k Ψ = Ψ)
    {g : G D n} (hg : proj D.sp.cm.sig (Jst D n) v g = 1) {y : hermA D n} (hy : IntAt v y) (X : Mx D W.rank n) :
    (ω g Ψ).1 X = pch ψ y.1 (ip W X X) * (ω g Ψ).1 X := by
  have e1 : ω (nb y * g) Ψ = ω g Ψ := by
    rw [nb_comm hnb hy.1 hy.2.1 hg, map_mul, Module.End.mul_apply, hΨ _ (nb_mem_KAt hnb hy)]
  have e2 := hω.unip (nb y) y.1 (hnb y) (ω g Ψ) X
  rw [map_mul, Module.End.mul_apply] at e1
  rw [e1] at e2
  exact e2

theorem ip_orbit (W : HSp D) (h : GA D W) (x : Matrix (Fin W.rank) (Fin n) D.host.E) :
    ip W (mm (Formalism.L2.Theta.mt W h) (rat x)) (mm (Formalism.L2.Theta.mt W h) (rat x)) = rat (gramQ W x) := by
  rw [show gramQ W x = GlobalTheory.Unf.gramQ W x from rfl, GlobalTheory.Unf.FB.rat_gramQ]
  simp only [ip, mm]
  rw [adj_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (gA W) (Formalism.L2.Theta.mt W h),
    ← Matrix.mul_assoc (adj (Formalism.L2.Theta.mt W h)), GlobalTheory.MixModel.mt_unitary]

theorem rank_gram_le (W : HSp D) (x : Matrix (Fin W.rank) (Fin n) D.host.E) : (gramQ W x).rank ≤ x.rank := by
  exact (Matrix.rank_mul_le_right _ _).trans (Matrix.rank_mul_le_right _ _)

theorem law0 {B : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χ θ} {μ : Measure (Mx D B.rank n)}
    {ω : G D n →* Module.End ℂ (schwartzA θ B.rank n)} (hω : IsWeilSch ψ χ θ B μ ω)
    (Φ : schwartzA θ B.rank n) (s : ℂ) (hs : (B.rank : ℂ) / 2 = s + (n : ℂ) / 2) :
    IsLaw χ s (fun g => (ω g Φ).1 0) := by
  intro q hq a ha g
  obtain ⟨m, u, b, e, hm, hu⟩ := GlobalTheory.StdUnn.LeftInvSect.exists_levi_unip hq a ha
  show (ω (q * g) Φ).1 0 = _ * _ * (ω g Φ).1 0
  have e' : ω (q * g) Φ = ω m (ω u (ω g Φ)) := by
    rw [e, map_mul, map_mul]; rfl
  have z1 : ∀ a : Mx D n n, ((0 : Mx D B.rank n) ⬝ a : Mx D B.rank n) = 0 := fun a => Matrix.zero_mul a
  have z2 : GlobalTheory.StdUnn.inner B (0 : Mx D B.rank n) 0 = 0 := by rw [GlobalTheory.StdUnn.inner, adj_zero, Matrix.zero_mul]
  rw [e', hω.levi m a hm, z1, hω.unip u b hu, z2, ← hs]
  simp [halfTr]

theorem resEta_add {χ : (AE D)ˣ →* Circle} {r : ℕ} (h : ResEta D χ r) (k : ℕ) : ResEta D χ (r + 2 * k) :=
  ⟨h.1, fun η hη a => by rw [h.2 η hη a, pow_add, pow_mul, Formalism.L2.Theta.eta_sq hη a, one_pow, mul_one]⟩

theorem conj_pch {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (x : hermA D n) (β : HermE D n) :
    conj (pch ψ x.1 (rat β.1)) = ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) x.1 : Mx D n n))) := by
  have ht : Matrix.trace (mm x.1 (rat β.1)) =
      Matrix.trace (HMul.hMul (β.1.map (incA D)) x.1 : Mx D n n) :=
    Matrix.trace_mul_comm _ _
  change conj (ψ (halfTr (Matrix.trace (mm x.1 (rat β.1))))) = _
  rw [ht, AddChar.map_neg_eq_inv, Complex.inv_eq_conj (hψ.2.1 _)]

theorem fc_eq {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (lam : Measure (hermA D n)) (𝓖 : Set (hermA D n))
    (nb : hermA D n → G D n) (F : G D n → ℂ) (β : HermE D n) (g : G D n) :
    fc ψ lam 𝓖 nb F β g = ∫ x in 𝓖, F (nb x * g) * conj (pch ψ x.1 (rat β.1)) ∂lam := by
  change (∫ b in 𝓖, F (nb b * g) * ψ (-halfTr ((β.1.map (incA D) * b.1).trace)) ∂lam) = _
  congr 1
  funext x
  rw [conj_pch hψ]

theorem cont_conj_pch {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (β : HermE D n) :
    Continuous fun x : hermA D n => conj (pch ψ x.1 (rat β.1)) :=
  Complex.continuous_conj.comp (hψ.1.comp (GlobalTheory.CompanionTheory.FourierN.continuous_halfTr.comp
    ((continuous_subtype_val.matrix_mul continuous_const).matrix_trace)))

theorem norm_conj_pch {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (x : hermA D n) (β : HermE D n) :
    ‖conj (pch ψ x.1 (rat β.1))‖ ≤ 1 := by
  rw [Complex.norm_conj]
  exact (hψ.2.1 _).le

theorem intOn {lam : Measure (hermA D n)} {𝓖 : Set (hermA D n)} (h : IsCovolOneH lam 𝓖) {f c : hermA D n → ℂ}
    (hf : Continuous f) (hp : ∀ γ ∈ ratHerm D n, ∀ x, f (γ + x) = f x) (hc : Continuous c) (hc1 : ∀ x, ‖c x‖ ≤ 1) :
    IntegrableOn (fun x => f x * c x) 𝓖 lam := by
  haveI : BorelSpace (Mx D n n) := ⟨rfl⟩
  haveI : BorelSpace (hermA D n) := Subtype.borelSpace _
  obtain ⟨K, hK, hcov⟩ := GlobalTheory.CompanionTheory.FourierN.exists_compact_cover (D := D) (n := n)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  have hb : ∀ x, ‖f x * c x‖ ≤ M := fun x => by
    obtain ⟨γ, hγ, hx⟩ := hcov x
    rw [norm_mul, ← hp γ hγ x]
    calc ‖f (γ + x)‖ * ‖c x‖ ≤ ‖f (γ + x)‖ * 1 := mul_le_mul_of_nonneg_left (hc1 x) (norm_nonneg _)
      _ ≤ M := by rw [mul_one]; exact hM _ hx
  refine Measure.integrableOn_of_bounded (M := M) ?_ (hf.mul hc).aestronglyMeasurable ?_
  · rw [h.2.2]; exact ENNReal.one_ne_top
  · exact Eventually.of_forall hb

end PositivityTheory.Rg.Rsw.L.LCutId

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LResCore
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L

open PositivityTheory.Rg.Rsw.L.LResCore

theorem resCore : Polar → CfFJ → IdemEx → GoodEv → FixW → WMaj → JPos → CfRel → CfInv → CutLow → CutId → ThBdd → ThCoef →
    IkSch → IkEq → ResCore := by
  classical
  intro hPolar hCfFJ hIdem hGoodEv hFixW hWMaj hJPos hCfRel hCfInv hCutLow hCutId hThBdd hThCoef hIkSch hIkEq
    D n t B W hd hn hbig hlt hpos ψ hψ χ hχ hη θ hθ μB μW hμB hμW ωB ωW hωB hωW H hH hHlev Φ U d E σ hcont ε hrad
  obtain ⟨dd⟩ := hd
  have hBr : B.rank = n + t := by have := dd.rank_add; omega
  have hηB : ResEta D χ B.rank := GlobalTheory.HeckeCharsOfSquare.resEta_of_mod hη (by omega)
  have hφc : Continuous (fun g => (ωB g Φ).1 0) :=
    (hWMaj D n B ψ hψ χ hχ hηB θ hθ μB hμB ωB hωB Φ).1.comp (continuous_id.prodMk continuous_const)
  have hφlaw : IsLaw χ ((t : ℂ) / 2) (fun g => (ωB g Φ).1 0) := isLaw_sw hBr hωB Φ
  obtain ⟨-, hP2, -⟩ := hPolar D n W.rank t hn hbig ψ hψ χ hχ hη (fun h0 => absurd h0 (by omega)) θ hθ H hH _ hφc hφlaw
    U d E σ hcont ε hrad
  obtain ⟨UH, hUHo, hUH⟩ := hHlev
  have : Submodule.IsLattice D.host.E (stdLattice D.host.E (n + n)) := isLattice_stdLattice
  obtain ⟨S₁, hS₁⟩ := GlobalTheory.PlaceGen.exists_levelOff_le D.sp.cm.sig (Jst D n) (stdLattice D.host.E (n + n)) UH hUHo
  obtain ⟨S₂, hS₂⟩ := hFixW D n B ψ hψ χ hχ hηB θ hθ μB hμB ωB hωB
  obtain ⟨S₃, hS₃⟩ := hGoodEv D θ hθ B.rank n Φ.1 Φ.2
  obtain ⟨nb, lam, 𝓖, hnb, hlam⟩ := GlobalTheory.CompanionTheory.SWCoef.coefDataExists D n
  obtain ⟨v, hvS, C, cc, hKill, hcd, hc0, hcut⟩ := hJPos D n W.rank t hn hpos ψ hψ χ hχ hη nb hnb (S₁ ∪ S₂ ∪ S₃)
  obtain ⟨e, he⟩ := (hIdem D (S₁ ∪ S₂ ∪ S₃)).1
  have hsub2 : S₂ ⊆ S₁ ∪ S₂ ∪ S₃ := fun x hx => by simp [hx]
  have hsub3 : S₃ ⊆ S₁ ∪ S₂ ∪ S₃ := fun x hx => by simp [hx]
  have hv1 : v ∉ S₁ := fun h => hvS (by simp [h])
  have hgood : Good (S₁ ∪ S₂ ∪ S₃) e Φ.1 := hS₃ _ hsub3 e he
  have hKΦ : ∀ k ∈ KAt D n v, ωB k Φ = Φ := fun k hk => hS₂ _ hsub2 e he Φ hgood k (kAt_le_kOff hvS hk)
  have hKH : ∀ k ∈ KAt D n v, ∀ g, H (g * k) = H g := fun k hk g =>
    hUH k (hS₁ (kAt_le_kOff hv1 hk)) (mem_atPts.1 (Subgroup.mem_inf.1 hk).2).1 g
  have hKφ : ∀ k ∈ KAt D n v, ∀ g, (ωB (g * k) Φ).1 0 = (ωB g Φ).1 0 := fun k hk g => by
    rw [map_mul, Module.End.mul_apply, hKΦ k hk]
  obtain ⟨νv, hνH, hνP⟩ := exists_haar_prob (KAt D n v) (isCompact_kAt v)
  have hfam : ∀ z g, ∫ k, cutR nb C (fam H (fun g => (ωB g Φ).1 0) ((t : ℂ) / 2) z) (g * k) ∂νv =
      cc z * fam H (fun g => (ωB g Φ).1 0) ((t : ℂ) / 2) z g := by
    intro z g
    refine hcut νv hνH hνP z _ (GlobalTheory.CompanionTheory.RswPolar.continuous_fam hH hφc _ z) (GlobalTheory.CompanionTheory.RswPolar.isLaw_fam hH hφlaw z) ?_ g
    intro k hk g'
    simp only [fam, hKH k hk g', hKφ k hk g']
  have hrel := hCfRel D n χ hχ H hH _ _ hφc hφlaw U d E σ hcont ε hrad nb hnb v C cc hcd νv hνP hfam
  obtain ⟨hcfCA, ⟨N, hN⟩, -⟩ := hCfFJ D n H _ _ U d E σ hcont ε hrad
  have hcfK : ∀ k, ∀ u ∈ KAt D n v, ∀ g, cf d E ((t : ℂ) / 2) ε k (g * u) = cf d E ((t : ℂ) / 2) ε k g :=
    fun k u hu g => hCfInv D n H _ _ U d E σ hcont ε hrad u (hKH u hu) (hKφ u hu) k g
  have hhigh : ∀ k, 2 ≤ k → cf d E ((t : ℂ) / 2) ε k = 0 := by
    have key : ∀ m k, 2 ≤ k → N < k + m → cf d E ((t : ℂ) / 2) ε k = 0 := by
      intro m
      induction m with
      | zero => intro k _ hk; exact hN k (by omega)
      | succ m ih =>
        intro k hk2 hkm
        have hj : ∀ j, k < j → cf d E ((t : ℂ) / 2) ε j = 0 := fun j hj => ih j (by omega) (by omega)
        have h1 := hrel k (by omega) hj
        have h2 := (hCutLow D n W.rank ψ hψ nb hnb v C hKill (cf d E ((t : ℂ) / 2) ε k) (hcfCA k).1 (hcfCA k).2
          (fun u hu g => hcfK k u hu g)).1 (hP2 k hk2)
        funext g
        have h3 := h1 g
        simp only [h2, Pi.zero_apply, integral_zero] at h3
        exact (mul_eq_zero.1 h3.symm).resolve_left hc0
    intro k hk
    exact key (N + 1) k hk (by omega)
  refine ⟨hhigh, ?_⟩
  intro X _ π _ cX κ hcX hcomp hκ hkill
  obtain ⟨a, ha⟩ := GlobalTheory.RegSch.exists_good_frameLat D B
  obtain ⟨νK, hνK, hνK1⟩ := exists_haar_prob _ ha.isCompact_K
  obtain ⟨μ₁, 𝓕₁, hμ₁⟩ := GlobalTheory.MixModel.exists_isCovolOne D t n
  have : LocallyCompactSpace (GA D W) := (GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D W).1
  let I : IkD dd n := IkD.mk _ ha νK hνK hνK1 μ₁ ⟨𝓕₁, hμ₁⟩ Measure.haar inferInstance
  obtain ⟨𝓕, h𝓕⟩ := GlobalTheory.FundDomDiscrete.exists_fundDom D W I.m I.haar
  let Ψ : schwartzA θ W.rank n := ⟨ikp I Φ.1, (hIkSch D n t B W dd I θ hθ Φ.1 Φ.2).2⟩
  let Ψ' : schwartzA θ W.rank n := ∑ x ∈ C.s, C.co x • ωW (nb x) Ψ
  have hStg : Stg dd hn ψ χ θ μB μW ωB ωW := ⟨hbig, hlt, hpos, hψ, hχ, hη, hθ, hμB, hμW, hωB, hωW⟩
  obtain ⟨κ', hκ'⟩ := hCutId D n t B W dd hn ψ χ θ μB μW ωB ωW hStg I H hH Φ U d E σ hcont ε hrad nb hnb v C hKill
    (fun k hk => ⟨hKΦ k hk, hKH k hk⟩) 𝓕 h𝓕 Ψ Ψ' rfl rfl
  have hΨinv : ∀ k ∈ KAt D n v, ωW k Ψ = Ψ := fun k hk => Subtype.ext (by
    rw [hIkEq D n t B W dd hn ψ χ θ μB μW ωB ωW hStg I Φ Ψ rfl k, hKΦ k hk])
  obtain ⟨hθc, -, -, hθb, -⟩ := hThBdd D n W ψ hψ χ hχ hη θ hθ μW hμW ωW hωW nb hnb v C hKill Ψ Ψ' hΨinv rfl
  have h𝓕fin : I.m 𝓕 ≠ ⊤ := (hThCoef D n W ψ hψ θ hθ I.m 𝓕 I.haar h𝓕 lam 𝓖 hlam Ψ.1 Ψ.2).1
  have : IsFiniteMeasure (I.m.restrict 𝓕) := isFiniteMeasure_restrict.2 h𝓕fin
  obtain ⟨b, hb⟩ := hθb _ (hcomp.mul (isCompact_kAt (n := n) v))
  have hbound : ∀ x (p : KAt D n v × GA D W), ‖theta ωW Ψ' (cX x * p.1) p.2‖ ≤ b := fun x p =>
    hb _ (Set.mul_mem_mul (subset_closure (Set.mem_range_self x)) p.1.2) p.2
  have hmeas : Measurable (fun q : X × (KAt D n v × GA D W) => theta ωW Ψ' (cX q.1 * q.2.1) q.2.2) :=
    hθc.measurable.comp (((hcX.comp measurable_fst).mul
      (measurable_subtype_coe.comp (measurable_fst.comp measurable_snd))).prodMk (measurable_snd.comp measurable_snd))
  have hintx : ∀ x, Integrable (fun p : KAt D n v × GA D W => theta ωW Ψ' (cX x * p.1) p.2)
      (νv.prod (I.m.restrict 𝓕)) := fun x =>
    Integrable.of_bound (hmeas.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable b
      (ae_of_all _ (hbound x))
  have hint : Integrable (Function.uncurry fun (x : X) (p : KAt D n v × GA D W) =>
      theta ωW Ψ' (cX x * p.1) p.2 * κ x) (π.prod (νv.prod (I.m.restrict 𝓕))) := by
    refine Integrable.mono' ((hκ.norm.const_mul b).comp_fst (νv.prod (I.m.restrict 𝓕)))
      (hmeas.aestronglyMeasurable.mul hκ.aestronglyMeasurable.comp_fst) (ae_of_all _ fun q => ?_)
    simp only [Function.uncurry, norm_mul]
    exact mul_le_mul_of_nonneg_right (hbound q.1 q.2) (norm_nonneg _)
  have hpt : ∀ x, cf d E ((t : ℂ) / 2) ε 1 (cX x) * κ x =
      (cc ((t : ℂ) / 2))⁻¹ * κ' * ∫ p, theta ωW Ψ' (cX x * p.1) p.2 * κ x ∂(νv.prod (I.m.restrict 𝓕)) := by
    intro x
    have h1 := hrel 1 le_rfl (fun j hj => hhigh j hj) (cX x)
    simp only [hκ'] at h1
    rw [integral_const_mul] at h1
    have e2 : ∫ p, theta ωW Ψ' (cX x * p.1) p.2 ∂(νv.prod (I.m.restrict 𝓕)) =
        ∫ u, ∫ h in 𝓕, theta ωW Ψ' (cX x * u) h ∂I.m ∂νv := integral_prod _ (hintx x)
    rw [integral_mul_const, e2, (eq_inv_mul_iff_mul_eq₀ hc0).2 h1.symm]
    ring
  have hzero : ∀ p : KAt D n v × GA D W, ∫ x, theta ωW Ψ' (cX x * p.1) p.2 * κ x ∂π = 0 := by
    intro p
    simp only [theta_mul]
    exact hkill (ωW p.1 Ψ') p.2
  simp only [hpt]
  rw [integral_const_mul, integral_integral_swap hint]
  simp only [hzero, integral_zero, mul_zero]

end PositivityTheory.Rg.Rsw.L

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.MatGExt
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

open GlobalTheory.CompanionTheory.JacobiMaps GlobalTheory.StdUnn.Model

namespace PositivityTheory.Rg.Rsw.L.UnitaryGroupMatrix

variable {D : D7} {n : ℕ}

theorem matG_mul (g h : G D n) : mat (g * h) = mat g * mat h := rfl

theorem matG_ext {g h : G D n} (e : mat g = mat h) : g = h := by
  apply Subtype.ext; apply Units.ext; exact e

theorem matG_inv {g : G D n} {M : Mx D (n + n) (n + n)} (h : mat g * M = 1) : mat g⁻¹ = M := by
  have e : mat g⁻¹ * mat g = 1 := by
    rw [← matG_mul, inv_mul_cancel]; rfl
  calc mat g⁻¹ = mat g⁻¹ * (mat g * M) := by rw [h, Matrix.mul_one]
    _ = M := by rw [← Matrix.mul_assoc, e, Matrix.one_mul]

theorem adjM_mul {a b c : ℕ} (x : Mx D a b) (y : Mx D b c) : adj (x * y) = adj y * adj x := by
  simp only [adj, Matrix.map_mul, Matrix.transpose_mul]

theorem adjM_one {a : ℕ} : adj (1 : Mx D a a) = 1 := by
  simp only [adj, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]

end PositivityTheory.Rg.Rsw.L.UnitaryGroupMatrix

namespace PositivityTheory.Rg.Rsw.L

open UnitaryGroupMatrix in

theorem geng : GenG := by
  intro D n A _ h1 hA
  let S : Subgroup (G D n) :=
    { carrier := {g | (∀ x ∈ A, g * x ∈ A) ∧ ∀ x ∈ A, g⁻¹ * x ∈ A}
      mul_mem' := fun {g h} hg hh =>
        ⟨fun x hx => by rw [mul_assoc]; exact hg.1 _ (hh.1 x hx),
         fun x hx => by rw [mul_inv_rev, mul_assoc]; exact hh.2 _ (hg.2 x hx)⟩
      one_mem' := ⟨fun x hx => by rwa [one_mul], fun x hx => by rwa [inv_one, one_mul]⟩
      inv_mem' := fun {g} hg => ⟨hg.2, fun x hx => by rw [inv_inv]; exact hg.1 x hx⟩ }
  have hS : S = ⊤ := by
    refine GlobalTheory.T.unitaryUnn_subgroup_eq_top_of_leviUnipotentWeyl D n S ?_ ?_ ?_
    · intro g a hg
      refine ⟨hA g (Or.inr (Or.inl ⟨a, hg⟩)), hA g⁻¹ (Or.inr (Or.inl ⟨a⁻¹, ?_⟩))⟩
      rw [inv_inv]
      apply matG_inv
      rw [hg, submatrix_fromBlocks_mul]
      simp only [mul_zero, zero_mul, add_zero, zero_add]
      rw [← adjM_mul, a.mul_inv, adjM_one, block_matrix_one]
    · intro g b hg
      refine ⟨hA g (Or.inl ⟨b, hg⟩), hA g⁻¹ (Or.inl ⟨-b, ?_⟩)⟩
      apply matG_inv
      rw [hg, submatrix_fromBlocks_mul]
      simp [block_matrix_one]
    · intro g hg
      have e : g⁻¹ = g * (g * g) := by
        apply matG_ext
        rw [matG_inv (M := blk4 0 (-1) 1 0), matG_mul, matG_mul, hg, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
        · simp
        · rw [hg, submatrix_fromBlocks_mul]; simp [block_matrix_one]
      have hw := hA g (Or.inr (Or.inr hg))
      refine ⟨hw, fun x hx => ?_⟩
      rw [e, mul_assoc, mul_assoc]
      exact hw _ (hw _ (hw x hx))
  ext g
  simp only [Set.mem_univ, iff_true]
  have hg : g ∈ S := hS ▸ Subgroup.mem_top g
  simpa using hg.1 1 h1

end PositivityTheory.Rg.Rsw.L

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.MemOfCoord
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LApproxId

open GlobalTheory.CompanionTheory.SiegelND.Coef.TestN

theorem memHA (D : D7) (t : ℕ) (X : Mx D t t) : X ∈ hermA D t ↔ X ∈ HermR (AF D.host.F) D.sp.cm.sig t := by
  constructor
  · intro h a c
    have h' : GlobalTheory.MixModel.adj X = X := h
    have := congrFun (congrFun h' a) c
    simpa [GlobalTheory.MixModel.adj, Matrix.transpose_apply, Matrix.map_apply] using this
  · intro h
    change GlobalTheory.MixModel.adj X = X
    ext a c
    simpa [GlobalTheory.MixModel.adj, Matrix.transpose_apply, Matrix.map_apply] using h a c

theorem smul_memA (D : D7) (t : ℕ) (e : AE D) (he : cA D e = e) (X : Mx D t t) (h : X ∈ hermA D t) :
    e • X ∈ hermA D t := by
  have h' : GlobalTheory.MixModel.adj X = X := h
  change GlobalTheory.MixModel.adj (e • X) = e • X
  ext a c
  have := congrFun (congrFun h' a) c
  simp only [GlobalTheory.MixModel.adj, Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
    map_mul, he] at this ⊢
  rw [this]

theorem pch_eq (D : D7) (t : ℕ) (ψ : AddChar (AF D.host.F) ℂ) (X T : Mx D t t) (hX : X ∈ hermA D t)
    (hT : T ∈ hermA D t) :
    pch ψ X T = ψ (pairHerm (AF D.host.F) D.sp.cm.sig t ⟨X, (memHA D t X).1 hX⟩ ⟨T, (memHA D t T).1 hT⟩) := by
  simp only [pch, halfTr, trA, pairHerm, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]

theorem coord_fix (D : D7) (t : ℕ) (e : AE D) (ε : AF D.host.F) (heS : e = algebraMap (AF D.host.F) (AE D) ε)
    {d : ℕ} (b : Module.Basis (Fin d) D.host.F D.host.E)
    (X : HermR (AF D.host.F) D.sp.cm.sig t) (hX : e • X.1 = X.1) (i : Idx t d) :
    ε * hCo (AF D.host.F) D.sp.cm.sig b X i = hCo (AF D.host.F) D.sp.cm.sig b X i :=
  (hCo_smul _ b ε X X (by rw [← heS, hX]) i).symm

theorem mem_of_coord (D : D7) (t : ℕ) (e : AE D) (ε : AF D.host.F) (heS : e = algebraMap (AF D.host.F) (AE D) ε)
    (hcA : cA D e = e) {d : ℕ} (b : Module.Basis (Fin d) D.host.F D.host.E)
    (eA : HermR (AF D.host.F) D.sp.cm.sig t ≃ₜ+ (Idx t d → AF D.host.F))
    (heA : ∀ X, eA X = hCo (AF D.host.F) D.sp.cm.sig b X) (y : HermR (AF D.host.F) D.sp.cm.sig t)
    (hw : ∀ i, ε * eA y i = eA y i) : e • y.1 = y.1 := by
  have hyA : y.1 ∈ hermA D t := (memHA D t y.1).2 y.2
  have hY := (memHA D t _).1 (smul_memA D t e hcA y.1 hyA)
  have h1 : eA ⟨e • y.1, hY⟩ = eA y := by
    funext i
    rw [heA, hCo_smul _ b ε y ⟨e • y.1, hY⟩ (by rw [← heS]) i, ← heA, hw]
  exact congrArg Subtype.val (eA.injective h1)

set_option synthInstance.maxHeartbeats 200000 in

theorem exTheta' (D : D7) (t : ℕ) (e : AE D) (ε : AF D.host.F) (heS : e = algebraMap (AF D.host.F) (AE D) ε)
    (hcA : cA D e = e) {d : ℕ} (b : Module.Basis (Fin d) D.host.F D.host.E)
    (eA : HermR (AF D.host.F) D.sp.cm.sig t ≃ₜ+ (Idx t d → AF D.host.F))
    (heA : ∀ X, eA X = hCo (AF D.host.F) D.sp.cm.sig b X) :
    ∃ Θ : hermS D t e ≃ₜ+ (Idx t d → fixE ε),
      ∀ x i, ((Θ x i) : AF D.host.F) = eA ⟨x.1.1, (memHA D t x.1.1).1 x.1.2⟩ i := by
  have hfix : ∀ (x : hermS D t e) i, ε * eA ⟨x.1.1, (memHA D t x.1.1).1 x.1.2⟩ i =
      eA ⟨x.1.1, (memHA D t x.1.1).1 x.1.2⟩ i := fun x i => by
    rw [heA]; exact coord_fix D t e ε heS b ⟨x.1.1, (memHA D t x.1.1).1 x.1.2⟩ x.2 i
  have hinv : ∀ v : Idx t d → fixE ε, e • (eA.symm (fun i => (v i).1)).1 = (eA.symm (fun i => (v i).1)).1 :=
    fun v => mem_of_coord D t e ε heS hcA b eA heA _ (fun i => by rw [eA.apply_symm_apply]; exact (v i).2)
  refine ⟨{ toFun := fun x i => ⟨eA ⟨x.1.1, (memHA D t x.1.1).1 x.1.2⟩ i, hfix x i⟩
            invFun := fun v => ⟨⟨(eA.symm (fun i => (v i).1)).1, (memHA D t _).2 (eA.symm _).2⟩, hinv v⟩
            left_inv := fun x => by
              apply Subtype.ext; apply Subtype.ext
              simp
            right_inv := fun v => by
              funext i
              apply Subtype.ext
              simp
            map_add' := fun x y => by
              funext i
              apply Subtype.ext
              change eA _ i = eA _ i + eA _ i
              exact congrFun (map_add eA ⟨x.1.1, (memHA D t x.1.1).1 x.1.2⟩ ⟨y.1.1, (memHA D t y.1.1).1 y.1.2⟩) i
            continuous_toFun := continuous_pi fun i => Continuous.subtype_mk ((continuous_apply i).comp
              (eA.continuous.comp ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _))) _
            continuous_invFun := ((continuous_subtype_val.comp (eA.symm.continuous.comp
              (continuous_pi fun i => continuous_subtype_val.comp (continuous_apply i)))).subtype_mk _).subtype_mk _ },
    fun x i => rfl⟩

theorem e_eq (D : D7) (S : Finset (Pl D)) (e : AE D) (he : IsIdem S e) :
    e = algebraMap (AF D.host.F) (AE D) ((1, LIdemEx.indS S) : AF D.host.F) := by
  have h : e = LIdemEx.eS S := LIdemEx.ae_ext _ _ (fun w => by rw [he.1 w, (LIdemEx.isIdem_eS S).1 w])
    (fun v => by rw [he.2 v, (LIdemEx.isIdem_eS S).2 v])
  exact h.trans rfl

end PositivityTheory.Rg.Rsw.L.LApproxId

end
end

