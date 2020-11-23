fn fact n ->
    fn iter (n, acc) ->
        if n == 0 then
            acc
        else
            iter(n - 1, n*acc)
        end
    end
    iter (n, 1)
end

fact 10
