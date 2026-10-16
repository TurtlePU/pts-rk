import Foundation
import PDFKit

let document = PDFDocument(url: URL(fileURLWithPath: CommandLine.arguments[1]))!
let pages = (0..<document.pageCount).map { document.page(at: $0)! }
let links = pages.flatMap { $0.annotations.compactMap { $0.url?.absoluteString } }
let expected = [
    "https://example.org/rocq/theories/ZFC_model/ModelSoundness.v#L133",
    "https://example.org/old/theories/Syntax.v#L7",
    "https://example.org/lean/Main.lean",
    "https://example.org/agda/Main.agda",
    "https://example.org/repo",
    "https://example.org/rocq/theories/Typing.v#L50",
    "https://example.org/rocq/theories/Proof.v",
]
guard links == expected else {
    fputs("PDF URL mismatch: \(links)\n", stderr)
    exit(1)
}
let text = pages.map { $0.string ?? "" }.joined(separator: "\n")
guard text.contains("Proof. An ordinary proof."),
      text.contains("Named proof. Grouped opening text."),
      text.contains("Proof. An opening group with"),
      text.contains("rocq-ai: is literal grouped opening text, not a badge."),
      !text.contains("\\begin{proof}") else {
    fputs("Proof environments were not rendered correctly\n", stderr)
    exit(1)
}
print("PDF URLs and proof environments: PASS")
