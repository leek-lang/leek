#![feature(is_ascii_octdigit)]
#![feature(const_trait_impl)]

pub mod backend;
pub mod common;
pub mod frontend;
pub mod middle;

// #[cfg(test)]
// mod test {
//    use crate::frontend::parse_file;
//
//    #[test]
//    fn run_examples() {
//        let files = std::fs::read_dir("../examples")
//            .unwrap()
//            .map(|f| f.unwrap());
//
//        for file in files {
//            parse_file(file.path()).unwrap();
//        }
//    }
//}
