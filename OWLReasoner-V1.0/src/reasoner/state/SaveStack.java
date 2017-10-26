package reasoner.state;

import java.io.Serializable;
import java.util.LinkedList;


public class SaveStack<T> {


  
    protected final LinkedList<T> list = new LinkedList<>();

    /**
     * @param depth
     *        depth
     * @return an object from a fixed depth
     */
    public T pop(int depth) {
        top(depth);
        return pop();
    }

    /**
     * @param depth
     *        depth
     * @return an object from a fixed depth
     */
    public T top(int depth) {
        assert list.size() >= depth;
        while (list.size() > depth) {
            pop();
        }
        return list.peek();
    }

    /** @return pop stack */
    public T pop() {
        assert !list.isEmpty();
        return list.pop();
    }
    public T pop1(int level) {
    		return list.get(level);
    }

    /**
     * @param e
     *        e
     */
    public void push(T e) {
        list.push(e);
    }
    public void push(T e, int level) {
        list.add(level, e);
    }

    /** clear the stack */
    public void clear() {
        list.clear();
    }

    /** @return true if is empty */
    public boolean isEmpty() {
        return list.isEmpty();
    }
    
    public int size() {
    		return list.size();
    }
}

