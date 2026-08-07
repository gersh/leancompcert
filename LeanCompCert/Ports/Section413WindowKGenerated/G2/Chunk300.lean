import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk300

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

def state06 : KState := ⟨⟨360582848448900926, 360582853884629043⟩, ⟨14495711452944286, 14606215312411720⟩, true⟩

def words05 : List Nat := [360583349372209770, 360583347608439192, 360583345844707434, 360583344717734332, 360583344147297401, 360583343297431210, 360583342447575439, 360583340920469085, 360583339802375251, 360583339786668711]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 30050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 30000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360554438950836534, 360554444390316630⟩, ⟨868469869563870887, 868580486226997099⟩, true⟩

def words06 : List Nat := [360583340266889933, 360583340267288671, 360583339663079305, 360583338207601474, 360583336752161263, 360583334524825250, 360583332853403109, 360583332030710994, 360583331208035121, 360583329674195147]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 30060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 30000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360579777969906691, 360579783413157516⟩, ⟨106434941652175898, 106545671719774766⟩, true⟩

def words07 : List Nat := [360583328854775044, 360583328996039076, 360583328996363007, 360583328924670586, 360583328701567840, 360583327541630888, 360583326381695517, 360583325700884441, 360583325607356106, 360583325490009903]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 30070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 30000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360605536612224137, 360605542059273892⟩, ⟨(-668840363993126711), (-668729519635212485)⟩, true⟩

def words08 : List Nat := [360583325372614347, 360583324526075119, 360583323511899036, 360583323257593958, 360583323003202011, 360583322002730163, 360583321086366639, 360583319606873034, 360583318127401608, 360583318486789255]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 30080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 30000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360568505421938094, 360568510872753428⟩, ⟨445750217301413419, 445861174984345637⟩, true⟩

def words09 : List Nat := [360583320325617918, 360583322164400621, 360583323134547832, 360583323500728425, 360583323501064179, 360583323258647284, 360583323873014232, 360583324027728906, 360583324028084764, 360583323536374171]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 30090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 30000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 30000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk300
