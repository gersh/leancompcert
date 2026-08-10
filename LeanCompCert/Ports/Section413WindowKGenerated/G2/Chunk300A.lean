import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk300A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360572590979021267, 360572596392130351⟩, ⟨323398018541461850, 323507843151647332⟩, true⟩

def state01 : KState := ⟨⟨360565557383484814, 360565562800347413⟩, ⟨534471631574214025, 534581568808897889⟩, true⟩

def words00 : List Nat := [360583379747231445, 360583379898193870, 360583379898548486, 360583379407265752, 360583378915950093, 360583377742436989, 360583377121870270, 360583377122242181, 360583377122573937, 360583376248158440]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 30000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 30000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360611812285062163, 360611817705680924⟩, ⟨(-853779467583902983), (-853669417608312587)⟩, true⟩

def words01 : List Nat := [360583376167539152, 360583376680566112, 360583378299515994, 360583379272839357, 360583379273210578, 360583379171458563, 360583379289783118, 360583380068193544, 360583381015807510, 360583381963446878]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 30010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 30000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360591855416434251, 360591860840851431⟩, ⟨(-254907360842140767), (-254797196820011031)⟩, true⟩

def words02 : List Nat := [360583382358000057, 360583382399345953, 360583382416738216, 360583382434244521, 360583382434578270, 360583382157739549, 360583380777727952, 360583378845377504, 360583376913079806, 360583376368245790]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 30020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 30000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360509016310836046, 360509021738998606⟩, ⟨2233327597124942517, 2233437873639898471⟩, true⟩

def words03 : List Nat := [360583377377741223, 360583378387245466, 360583378701671800, 360583378702070122, 360583377913673808, 360583376845222802, 360583375776732164, 360583374643551989, 360583373011053488, 360583370536390081]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 30030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 30000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360556552210731274, 360556557642653614⟩, ⟨805007864445661702, 805118253923275486⟩, true⟩

def words04 : List Nat := [360583368061803706, 360583365757692911, 360583364004079678, 360583362573749042, 360583361143475198, 360583358761787167, 360583355595331670, 360583353532339626, 360583351469368476, 360583350263416452]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 30040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 30000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk300A
