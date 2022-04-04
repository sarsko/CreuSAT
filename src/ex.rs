extern crate creusot_contracts;
use creusot_contracts::*;
use creusot_contracts::std::*;


pub struct Formula {
    pub clauses: Vec<usize>,
    pub num_vars: usize,
}

pub trait Bing {
    fn bing(self) -> usize;
}

/*
pub trait Model {
    type ModelTy;
    #[logic]
    fn model(self) -> Self::ModelTy;
}

impl<T: Model + ?Sized> Model for &T {
    type ModelTy = T::ModelTy;
    #[logic]
    fn model(self) -> Self::ModelTy {
        (*self).model()
    }
}
*/
impl<T> Bing for Vec<T> {
    fn bing(self) -> usize {
        0
    }

}

impl<T: Bing + ?Sized> Bing for &T {
    fn bing(self) -> usize {
        0
    }
}

/*
impl<T: Bing + ?Sized> Bing for &mut T {
    fn bing(self) -> usize {
        (*self).bing()
    }
}
*/



#[ensures((*u).model()=== @u)]
fn main(u: &&&&&&&&&&&&&&&&usize)  {
}

fn main3(u: & Vec<usize>)  {
    let b = u.bing();
}