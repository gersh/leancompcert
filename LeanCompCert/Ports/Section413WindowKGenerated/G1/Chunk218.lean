import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk218

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362494664866206183, 362494671276442463⟩, ⟨(-231573148205811019), (-231478647362420477)⟩, true⟩

def state01 : KState := ⟨⟨362469351062189058, 362469357478561529⟩, ⟨320310516535927189, 320405151179826551⟩, true⟩

def words00 : List Nat := [371284053939957448, 371284053940642784, 371284053241200162, 371284053942042442, 371284054643178989, 371284054643859987, 371284052545832418, 371284050459282617, 371284048372638946, 371284048223686693]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 21800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 21800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362436373860777170, 362436380283286527⟩, ⟨1039888968885217899, 1039983737405665085⟩, true⟩

def words01 : List Nat := [371284048189560381, 371284048829205917, 371284049101677085, 371284049102361642, 371284047370580070, 371284046282629611, 371284046202818878, 371284046203500324, 371284044416421101, 371284042232755165]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 21810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 21800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362484589020626929, 362484595449238035⟩, ⟨(-12250296496796835), (-12155394805547551)⟩, true⟩

def words02 : List Nat := [371284040048994261, 371284039962126971, 371284039530726237, 371284040233472519, 371284040440708350, 371284040441401767, 371284038915832784, 371284038208070661, 371284038627881239, 371284038654093262]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 21820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 21800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362468857931455136, 362468864366296083⟩, ⟨331229421086479075, 331324458805636109⟩, true⟩

def words03 : List Nat := [371284038654604456, 371284038599996970, 371284039349574984, 371284039350332869, 371284039105184033, 371284038922922407, 371284038740454562, 371284038381769968, 371284035593906363, 371284034900124180]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 21830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 21800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362448048641161048, 362448055082072863⟩, ⟨785903561783949198, 785998732122633346⟩, true⟩

def words04 : List Nat := [371284035604698859, 371284035605381308, 371284034591075965, 371284033543372924, 371284032495512819, 371284031596545022, 371284029944861792, 371284029152783518, 371284028360542360, 371284027564092206]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 21840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 21800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362519923806141166, 362519930253213886⟩, ⟨(-784898745843081224), (-784803440856749048)⟩, true⟩

def words05 : List Nat := [371284026363561386, 371284026809604070, 371284028265541060, 371284028266235673, 371284028027728989, 371284027571088471, 371284027709524325, 371284027710276114, 371284028905662997, 371284030548678104]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 21850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 21800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362506485866249637, 362506492319498747⟩, ⟨(-491201782592516027), (-491106342559167119)⟩, true⟩

def words06 : List Nat := [371284031716358718, 371284031717043461, 371284031908174040, 371284033048965546, 371284034828572247, 371284034985399478, 371284035017206505, 371284035049251551, 371284036610319385, 371284037637839968]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 21860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 21800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362458817980433225, 362458824439832219⟩, ⟨551792004791347356, 551887579354740446⟩, true⟩

def words07 : List Nat := [371284040752800364, 371284043867761403, 371284046835994002, 371284047021850176, 371284047310791174, 371284047600025465, 371284049676832419, 371284049677515760, 371284048973058064, 371284047820972747]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 21870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 21800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362501412211674835, 362501418677201514⟩, ⟨(-380153512629159058), (-380057803961352114)⟩, true⟩

def words08 : List Nat := [371284047601869745, 371284047774300055, 371284049784015728, 371284051793818384, 371284053459869605, 371284053460553749, 371284053867907968, 371284054930199659, 371284056510936052, 371284057304767119]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 21880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 21800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362510234690627748, 362510241162372833⟩, ⟨(-573217573705358510), (-573121728885464110)⟩, true⟩

def words09 : List Nat := [371284058093342566, 371284058882073215, 371284061753901771, 371284063722130589, 371284066006022578, 371284068289988299, 371284070545181523, 371284070545865680, 371284071219575607, 371284072415334549]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 21890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 21800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 21800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk218
