pub mod ai;
pub mod ast;
pub mod ir;
pub mod tc;
pub mod compiler;

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}
