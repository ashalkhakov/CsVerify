using System;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;

namespace CsVerify.Verifier
{
    /// <summary>
    /// The services a context asks its host for where its model is built (the application's service provider, which
    /// DbContextOptionsBuilder.UseApplicationServiceProvider names: `this.GetService&lt;T&gt;()` in OnModelCreating). The
    /// host isn't here. A service that may be a host's (not EF's, nor of what EF builds on, nor the runtime's) is an
    /// implementation among the program's assemblies, made by a constructor whose arguments are services in turn;
    /// where there is none and the service is an interface, a stand-in, each of whose members answers with its type's
    /// default: false, 0, null (StoodIn names it). Any other service is absent, as without a host: EF's logging, its
    /// cache.
    /// </summary>
    internal sealed class EfHostServices : IServiceProvider
    {
        private readonly Func<Type, bool> _hosts;
        private readonly Func<IEnumerable<Assembly>> _program;
        private readonly Func<Type> _standIn;
        private readonly Dictionary<Type, object> _made = new Dictionary<Type, object>();
        private readonly HashSet<Type> _making = new HashSet<Type>();
        private List<Type> _classes;

        /// <summary>The services stood in for, in the order they were asked for.</summary>
        public readonly List<string> StoodIn = new List<string>();

        /// <param name="standIn">A stand-in's base, a DispatchProxy: of the program's load context, as the services are.</param>
        public EfHostServices(Func<Type, bool> hosts, Func<IEnumerable<Assembly>> program, Func<Type> standIn)
        {
            _hosts = hosts;
            _program = program;
            _standIn = standIn;
        }

        public object GetService(Type service)
        {
            lock (_made)
            {
                if (Environment.GetEnvironmentVariable("CSVERIFY_EF_MODEL_TRACE") == "2")
                {
                    Console.Error.WriteLine($"[ef-model] asked of the host: {service}");
                }
                if (service == null || service.ContainsGenericParameters || !_hosts(service))
                {
                    return null;
                }
                if (_made.TryGetValue(service, out var made))
                {
                    return made;
                }
                if (!_making.Add(service))
                {
                    return null;
                }
                try
                {
                    made = Implementation(service);
                    if (made == null && service.IsInterface)
                    {
                        made = DispatchProxy.Create(service, _standIn());
                        StoodIn.Add(Display(service));
                    }
                    return _made[service] = made;
                }
                catch (Exception e)
                {
                    if (Environment.GetEnvironmentVariable("CSVERIFY_EF_MODEL_TRACE") != null)
                    {
                        Console.Error.WriteLine($"[ef-model] no stand-in for {Display(service)}: {e.GetType().Name}: {e.Message.Split('\n')[0]}");
                    }
                    return _made[service] = null;
                }
                finally
                {
                    _making.Remove(service);
                }
            }
        }

        private object Implementation(Type service)
        {
            _classes ??= _program().SelectMany(Types).Where(c => c.IsClass && !c.IsAbstract).OrderBy(c => c.FullName, StringComparer.Ordinal).ToList();
            foreach (var c in _classes)
            {
                var type = c;
                if (c.IsGenericTypeDefinition)
                {
                    // (C<T> for I<T>: closed over the service's arguments)
                    if (!service.IsConstructedGenericType || c.GetGenericArguments().Length != service.GenericTypeArguments.Length)
                    {
                        continue;
                    }
                    try
                    {
                        type = c.MakeGenericType(service.GenericTypeArguments);
                    }
                    catch (Exception)
                    {
                        continue;
                    }
                }
                if (!service.IsAssignableFrom(type))
                {
                    continue;
                }
                foreach (var ctor in type.GetConstructors().OrderBy(k => k.GetParameters().Length))
                {
                    try
                    {
                        return ctor.Invoke(ctor.GetParameters().Select(p =>
                            GetService(p.ParameterType) ?? (p.HasDefaultValue ? p.DefaultValue : p.ParameterType.IsValueType ? Activator.CreateInstance(p.ParameterType) : null)).ToArray());
                    }
                    catch (Exception)
                    {
                    }
                }
            }
            return null;
        }

        private static IEnumerable<Type> Types(Assembly a)
        {
            try
            {
                return a.GetTypes();
            }
            catch (ReflectionTypeLoadException e)
            {
                return e.Types.Where(t => t != null);
            }
        }

        private static string Display(Type t) =>
            !t.IsGenericType ? t.FullName ?? t.Name
            : (t.GetGenericTypeDefinition().FullName ?? t.Name).Split('`')[0] + "<" + string.Join(", ", t.GenericTypeArguments.Select(Display)) + ">";
    }
}
